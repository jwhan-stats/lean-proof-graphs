import Lean
import Lean.Elab.InfoTree
import Lean.Meta.CollectFVars

open Lean Meta Elab

namespace DependencyGraph

/-!
`graph_exporter` elaborates one reconstructed rollout proof and exports the
proposition-valued local bindings that Lean actually accepted.  The Python
postprocessor turns this lossless, proof-term-facing layer into the smaller
manifest dependency hypergraph used in the presentation.
-/

structure LocalBinding where
  fvarId   : FVarId
  userName : Name
  type     : Expr
  value    : Expr
  lctx     : LocalContext
  ctx      : ContextInfo
  parent?  : Option Name

private structure CollectState where
  acc : Array LocalBinding := #[]

private def pushFromLCtx (lctx : LocalContext) (ctx : ContextInfo)
    (st : CollectState) : CollectState :=
  lctx.getFVarIds.foldl
    (init := st)
    (fun state fvarId =>
      match lctx.find? fvarId with
      | none => state
      | some decl =>
          match decl.value? true with
          | none => state
          | some value =>
              { acc := state.acc.push {
                  fvarId := fvarId
                  userName := decl.userName
                  type := decl.type
                  value := value
                  lctx := lctx
                  ctx := ctx
                  parent? := ctx.parentDecl?
                } })

private partial def collectFromTree
    (tree : InfoTree) (ctx? : Option ContextInfo)
    (st : CollectState) : CollectState :=
  match tree with
  | .context ctx child =>
      collectFromTree child (ctx.mergeIntoOuter? ctx?) st
  | .node info children =>
      let st :=
        match ctx? with
        | some ctx =>
            match info with
            | .ofTermInfo termInfo => pushFromLCtx termInfo.lctx ctx st
            | _ => st
        | none => st
      let childCtx? := info.updateContext? ctx?
      children.foldl (fun state child => collectFromTree child childCtx? state) st
  | .hole _ => st

private def dedupBindings (items : Array LocalBinding) : Array LocalBinding :=
  Id.run do
    let mut seen : Std.HashSet FVarId := {}
    let mut out : Array LocalBinding := #[]
    for item in items.toList.reverse do
      if !seen.contains item.fvarId then
        seen := seen.insert item.fvarId
        out := out.push item
    return out.reverse

private def collectLocals (trees : Array InfoTree) : Array LocalBinding :=
  dedupBindings <| (trees.foldl (fun st tree => collectFromTree tree none st) {}).acc

private partial def collectConstNames
    (expr : Expr) (acc : Std.HashSet Name := {}) : Std.HashSet Name :=
  match expr with
  | .const name _ => acc.insert name
  | .app fn arg => collectConstNames arg (collectConstNames fn acc)
  | .lam _ type body _ => collectConstNames body (collectConstNames type acc)
  | .forallE _ domain body _ => collectConstNames body (collectConstNames domain acc)
  | .letE _ type value body _ =>
      collectConstNames body (collectConstNames value (collectConstNames type acc))
  | .mdata _ body => collectConstNames body acc
  | .proj _ _ body => collectConstNames body acc
  | .sort _ | .lit _ | .bvar _ | .fvar _ | .mvar _ => acc

private def theoremRuleNames (env : Environment) (expr : Expr) : Array String :=
  let names := (collectConstNames expr).toArray.filter fun name =>
    match env.find? name with
    | some (.thmInfo _) =>
        let text := name.toString
        !text.startsWith "_" && !text.contains ".match_"
    | _ => false
  (names.map Name.toString).qsort (fun left right => left < right)

private def ppExprString (expr : Expr) : MetaM String := do
  let options := (← getOptions).setBool `pp.universes false
  let options := options.setBool `pp.proofs false
  let options := options.setBool `pp.fullNames false
  return (← withOptions (fun _ => options) <| ppExpr expr).pretty

private def propJson (name statement origin : String)
    (fvarId? : Option FVarId := none) : Json :=
  Json.mkObj ([
    ("name", toJson name),
    ("statement", toJson statement),
    ("origin", toJson origin)
  ] ++ match fvarId? with
    | some fvarId => [("fvar_id", toJson fvarId.name.toString)]
    | none => [])

private def usedPropFVars (expr : Expr) : MetaM (Array Json) := do
  let (_, state) ← expr.collectFVars.run ({} : Lean.CollectFVars.State)
  let used := state.fvarSet
  let lctx ← getLCtx
  let mut result : Array Json := #[]
  for fvarId in lctx.getFVarIds do
    if used.contains fvarId then
      match lctx.find? fvarId with
      | none => pure ()
      | some decl =>
          let type ← instantiateMVars decl.type
          if ← isProp type then
            let statement ← ppExprString type
            let origin := if (decl.value? true).isSome then "derived" else "local_assumption"
            result := result.push
              (propJson decl.userName.toString statement origin (some fvarId))
  return result

private def edgeJson
    (env : Environment) (edgeId parent conclusionName : String)
    (conclusionType proof : Expr) (source : String)
    (conclusionFVarId? : Option FVarId := none) : MetaM Json := do
  -- Info-tree local contexts may still mention assigned metavariables even
  -- though the proof expression itself is fully instantiated.  Normalize the
  -- whole context before asking the kernel to check the local witness.
  let lctx ← instantiateLCtxMVars (← getLCtx)
  withLCtx' lctx do
    let conclusionType ← instantiateMVars conclusionType
    let proof ← instantiateMVars proof
    if conclusionType.hasMVar || proof.hasMVar then
      throwError m!"dependency edge {parent}/{edgeId} ({conclusionName}) contains unresolved metavariables (conclusion: {conclusionType.hasMVar}, witness: {proof.hasMVar}, source: {source})"
    -- This is deliberately a kernel check, not just a successful elaborator
    -- result.  It checks the witness in the exact local context from which the
    -- proposition-valued binding was extracted.
    checkWithKernel proof
    let proofType ← inferType proof
    unless ← isDefEq proofType conclusionType do
      throwError "dependency edge witness type is not definitionally equal to its conclusion"
    let conclusion ← ppExprString conclusionType
    let proofTypeText ← ppExprString proofType
    let premises ← usedPropFVars proof
    let rules := theoremRuleNames env proof
    return Json.mkObj [
      ("id", toJson edgeId),
      ("parent", toJson parent),
      ("source", toJson source),
      ("conclusion", propJson conclusionName conclusion "derived" conclusionFVarId?),
      ("premises", toJson premises),
      ("rule_items", toJson rules),
      ("witness_check", Json.mkObj [
        ("kernel_typecheck", toJson true),
        ("conclusion_defeq_proof_type", toJson true),
        ("contains_unresolved_metavariables", toJson false),
        ("proof_type", toJson proofTypeText)
      ])
    ]

private def analyzeBinding (env : Environment) (index : Nat)
    (binding : LocalBinding) : IO (Option Json × Option Json) :=
  binding.ctx.runMetaM binding.lctx do
    let lctx ← instantiateLCtxMVars (← getLCtx)
    withLCtx' lctx do
      let type ← instantiateMVars binding.type
      let parent := binding.parent?.map Name.toString |>.getD "_anonymous_"
      let edgeId := s!"local_{index}"
      if type.hasMVar then
        let statement ← ppExprString type
        return (none, some <| Json.mkObj [
          ("id", toJson edgeId),
          ("parent", toJson parent),
          ("binding_name", toJson binding.userName.toString),
          ("fvar_id", toJson binding.fvarId.name.toString),
          ("candidate_type", toJson statement),
          ("source", toJson "info_tree_local_binding"),
          ("reason", toJson "unresolved_metavariables_in_candidate_type"),
          ("policy", toJson "not_emitted_as_dependency_edge")
        ])
      if !(← isProp type) then
        return (none, none)
      let proof ← instantiateMVars binding.value
      if proof.hasMVar then
        let statement ← ppExprString type
        return (none, some <| Json.mkObj [
          ("id", toJson edgeId),
          ("parent", toJson parent),
          ("binding_name", toJson binding.userName.toString),
          ("fvar_id", toJson binding.fvarId.name.toString),
          ("candidate_type", toJson statement),
          ("source", toJson "info_tree_local_binding"),
          ("reason", toJson "unresolved_metavariables_in_candidate_witness"),
          ("policy", toJson "not_emitted_as_dependency_edge")
        ])
      return (some (← edgeJson env edgeId parent binding.userName.toString
        type proof "info_tree_local_binding" (some binding.fvarId)), none)

private def analyzeMain (env : Environment) (theoremName : Name)
    (info : TheoremVal) : MetaM (Array Json × Array Json × Json × Json) := do
  lambdaLetTelescope info.value fun params body => do
    let mut manifest : Array Json := #[]
    let mut localEdges : Array Json := #[]
    let mut index := 0
    for param in params do
      let fvarId := param.fvarId!
      let type ← inferType param
      let lctx ← getLCtx
      if ← isProp type then
        match lctx.find? fvarId with
        | some decl =>
            match decl.value? true with
            | none =>
                let statement ← ppExprString type
                manifest := manifest.push
                  (propJson decl.userName.toString statement "manifest" (some fvarId))
            | some value =>
                localEdges := localEdges.push (← edgeJson env s!"telescope_{index}"
                  theoremName.toString decl.userName.toString type value
                  "theorem_value_telescope" (some fvarId))
        | none => pure ()
      index := index + 1

    let goalType ← inferType body
    let goalStatement ← ppExprString goalType
    let finalEdge ← edgeJson env "goal_edge" theoremName.toString "goal"
      goalType body "elaborated_theorem_body"
    return (manifest, localEdges, propJson "goal" goalStatement "goal", finalEdge)

private def runMetaIO (env : Environment) (action : MetaM α) : IO α := do
  let coreCtx : Core.Context := {
    options := {}
    fileName := "<dependency-graph-exporter>"
    fileMap := FileMap.ofString ""
  }
  let coreState : Core.State := {
    env := env
    nextMacroScope := 1
    ngen := default
    traceState := default
    cache := default
    messages := default
    infoState := default
    snapshotTasks := #[]
  }
  let (value, _, _) ← action.toIO coreCtx coreState ({} : Meta.Context) ({} : Meta.State)
  return value

private unsafe def elaborateFile (path : System.FilePath) :
    IO (Environment × PersistentArray InfoTree × MessageLog) := do
  Lean.enableInitializersExecution
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path.toString
  let options : Options := ({} : Options)
    |>.setBool `Elab.async false
  let options := Lean.internal.cmdlineSnapshots.setIfNotSet options true
  let mainModuleName := (path.fileStem.getD "RolloutProof").toName
  let setup stx := do
    return .ok {
      imports := stx.imports
      isModule := stx.isModule
      mainModuleName := mainModuleName
      opts := options
      trustLevel := 0
      plugins := #[]
    }
  let snapshot ← Language.Lean.process setup none { inputCtx with }
  let snapshots := Language.toSnapshotTree snapshot
  let allSnapshots := snapshots.getAll
  let messages := allSnapshots.map (·.diagnostics.msgLog) |>.foldl (· ++ ·) {}
  let trees := allSnapshots.flatMap (fun snap =>
    match snap.infoTree? with
    | some tree => #[tree]
    | none => #[]) |>.toPArray'
  let some commandState := Language.Lean.waitForFinalCmdState? snapshot
    | do
      for message in messages.toArray do
        IO.eprintln (← message.toString)
      throw <| IO.Error.userError "failed to obtain the final Lean command state"
  return (commandState.env, trees, messages)

private def messageStrings (messages : MessageLog) : IO (Array String) := do
  let mut result : Array String := #[]
  for message in messages.toArray do
    result := result.push (← message.toString)
  return result

unsafe def exportGraph (inputPath outputPath : String) (theoremTexts : List String) : IO UInt32 := do
  let _ ← Lean.initSearchPath (← Lean.findSysroot)
  let (env, trees, messages) ← elaborateFile (System.FilePath.mk inputPath)
  let diagnostics ← messageStrings messages
  if messages.hasErrors then
    for diagnostic in diagnostics do
      IO.eprintln diagnostic
    return 1

  let mut theoremResults : Array Json := #[]
  for theoremText in theoremTexts do
    let theoremName := theoremText.toName
    let theoremInfo ←
      match env.find? theoremName with
      | some (.thmInfo info) => pure info
      | some _ =>
          IO.eprintln s!"{theoremText} is not a theorem"
          return 2
      | none =>
          IO.eprintln s!"theorem not found after elaboration: {theoremText}"
          return 2
    let (manifest, telescopeEdges, goal, finalEdge) ←
      runMetaIO env (analyzeMain env theoremName theoremInfo)
    let axioms ← runMetaIO env (Lean.collectAxioms theoremName)
    let axiomNames := (axioms.map Name.toString).qsort (fun left right => left < right)
    theoremResults := theoremResults.push <| Json.mkObj [
      ("theorem_name", toJson theoremText),
      ("manifest", toJson manifest),
      ("local_edges", toJson telescopeEdges),
      ("goal", goal),
      ("final_edge", finalEdge),
      ("axioms", toJson axiomNames)
    ]

  let bindings := collectLocals trees.toArray
  let requestedTheorems : Std.HashSet Name := theoremTexts.foldl
    (fun names theoremText => names.insert theoremText.toName) {}
  let mut localEdges : Array Json := #[]
  let mut excludedLocalBindings : Array Json := #[]
  let mut index := 0
  for binding in bindings do
    let requestedParent := binding.parent?.map requestedTheorems.contains |>.getD false
    if requestedParent then
      let (edge?, excluded?) ← analyzeBinding env index binding
      if let some edge := edge? then
        localEdges := localEdges.push edge
      if let some excluded := excluded? then
        excludedLocalBindings := excludedLocalBindings.push excluded
    index := index + 1

  let output := Json.mkObj [
    ("schema_version", toJson "lean_proof_term_projection_raw_v4"),
    ("lean_version", toJson Lean.versionString),
    ("theorems", toJson theoremResults),
    ("local_edges", toJson localEdges),
    ("excluded_local_bindings", toJson excludedLocalBindings),
    ("diagnostics", toJson diagnostics)
  ]
  IO.FS.writeFile outputPath output.pretty
  IO.println s!"[graph_exporter] wrote {outputPath} ({localEdges.size} local proposition bindings)"
  return 0

end DependencyGraph

unsafe def main (args : List String) : IO UInt32 :=
  match args with
  | inputPath :: outputPath :: theoremNames => do
      if theoremNames.isEmpty then
        IO.eprintln "at least one theorem name is required"
        pure 2
      else
        DependencyGraph.exportGraph inputPath outputPath theoremNames
  | _ => do
      IO.eprintln "usage: graph_exporter <input.lean> <output.json> <theorem-name> [theorem-name ...]"
      pure 2
