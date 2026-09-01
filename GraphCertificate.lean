import Lean
import Lean.Meta.CollectFVars

open Lean Meta Elab Command

namespace DependencyGraphCertificate

/-!
`#check_dependency_graph` replays a concrete dependency manifest against the
elaborated value of a theorem in the same file.  Each selected witness is
kernel-checked in its theorem-local context before its direct proposition
dependencies and conclusion are compared with the embedded manifest.
-/

structure PropRecord where
  name : String
  statement : String
  deriving FromJson, Repr, BEq, DecidableEq, Inhabited

structure ExpectedEdge where
  graphEdgeId : String
  rawEdgeId : String
  premises : Array PropRecord
  conclusion : PropRecord
  deriving FromJson, Repr

structure ExpectedGraph where
  graphId : String
  theoremName : String
  topologySha256 : String
  reconstructedProofSha256 : String
  selectedEdgeCount : Nat
  edges : Array ExpectedEdge
  deriving FromJson, Repr

private structure CheckedEdge where
  rawEdgeId : String
  premises : Array PropRecord
  conclusion : PropRecord
  deriving Inhabited

private def normalizeWhitespace (value : String) : String :=
  String.intercalate " " <|
    (value.split Char.isWhitespace).toList.map (·.toString) |>.filter (· != "")

private def ppExprString (expr : Expr) : MetaM String := do
  let options := (← getOptions).setBool `pp.universes false
  let options := options.setBool `pp.proofs false
  let options := options.setBool `pp.fullNames false
  let rendered ←
    withTheReader Core.Context
      (fun context => {
        context with currNamespace := .anonymous, openDecls := []
      }) <| withOptions (fun _ => options) <| ppExpr expr
  return normalizeWhitespace rendered.pretty

private def propRecord (name : String) (type : Expr) : MetaM PropRecord := do
  let name :=
    if name.startsWith "inst._@" then
      "<generated-instance>"
    else if name.contains "._@._internal." then
      "<generated-internal>"
    else
      name
  return { name := name, statement := ← ppExprString type }

private def usedPropFVars (expr : Expr) : MetaM (Array PropRecord) := do
  let (_, state) ← expr.collectFVars.run ({} : Lean.CollectFVars.State)
  let used := state.fvarSet
  let lctx ← getLCtx
  let mut result : Array PropRecord := #[]
  for fvarId in lctx.getFVarIds do
    if used.contains fvarId then
      match lctx.find? fvarId with
      | none => pure ()
      | some decl =>
          let type ← instantiateMVars decl.type
          if ← isProp type then
            result := result.push (← propRecord decl.userName.toString type)
  return result

private def checkedEdge (rawEdgeId conclusionName : String)
    (conclusionType proof : Expr) : MetaM CheckedEdge := do
  let lctx ← instantiateLCtxMVars (← getLCtx)
  withLCtx' lctx do
    let conclusionType ← instantiateMVars conclusionType
    let proof ← instantiateMVars proof
    if conclusionType.hasMVar || proof.hasMVar then
      throwError m!"dependency edge {rawEdgeId} contains unresolved metavariables"
    checkWithKernel proof
    let proofType ← inferType proof
    unless ← isDefEq proofType conclusionType do
      throwError m!"dependency edge {rawEdgeId} witness type differs from its conclusion"
    return {
      rawEdgeId := rawEdgeId
      premises := ← usedPropFVars proof
      conclusion := ← propRecord conclusionName conclusionType
    }

private def analyzeTheorem (info : TheoremVal) : MetaM (Array CheckedEdge) :=
  lambdaLetTelescope info.value fun params body => do
    let mut edges : Array CheckedEdge := #[]
    let mut index := 0
    for param in params do
      let fvarId := param.fvarId!
      let type ← inferType param
      let lctx ← getLCtx
      if ← isProp type then
        match lctx.find? fvarId with
        | some decl =>
            if let some value := decl.value? true then
              edges := edges.push (← checkedEdge s!"telescope_{index}"
                decl.userName.toString type value)
        | none => pure ()
      index := index + 1
    let goalType ← inferType body
    edges := edges.push (← checkedEdge "goal_edge" "goal" goalType body)
    return edges

private def runMetaIO (env : Environment) (action : MetaM α) : IO α := do
  let coreCtx : Core.Context := {
    options := {}
    fileName := "<dependency-graph-certificate>"
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
  let (value, _, _) ← action.toIO coreCtx coreState
    ({} : Meta.Context) ({} : Meta.State)
  return value

private def hasDuplicates (items : Array String) : Bool := Id.run do
  let mut seen : Std.HashSet String := {}
  for item in items do
    if seen.contains item then
      return true
    seen := seen.insert item
  return false

private def checkExpectedGraph
    (expected : ExpectedGraph) (actual : Array CheckedEdge) : MetaM Unit := do
  if expected.selectedEdgeCount != expected.edges.size then
    throwError "selectedEdgeCount differs from the embedded edge array size"
  if expected.edges.isEmpty then
    throwError "a dependency certificate must contain at least the goal edge"
  if hasDuplicates (expected.edges.map (·.graphEdgeId)) then
    throwError "the embedded certificate has duplicate graph edge ids"
  if hasDuplicates (expected.edges.map (·.rawEdgeId)) then
    throwError "the embedded certificate has duplicate raw edge ids"
  unless expected.edges.any (·.rawEdgeId == "goal_edge") do
    throwError "the embedded certificate does not select the theorem goal edge"
  for edge in expected.edges do
    let matchingEdges := actual.filter (·.rawEdgeId == edge.rawEdgeId)
    if matchingEdges.size != 1 then
      throwError m!"graph edge {edge.graphEdgeId}: raw witness {edge.rawEdgeId} occurs {matchingEdges.size} times"
    let witness := matchingEdges[0]!
    if edge.premises != witness.premises then
      throwError m!"graph edge {edge.graphEdgeId}: premise mismatch\nexpected: {repr edge.premises}\nactual: {repr witness.premises}"
    if edge.conclusion != witness.conclusion then
      throwError m!"graph edge {edge.graphEdgeId}: conclusion mismatch\nexpected: {repr edge.conclusion}\nactual: {repr witness.conclusion}"

syntax (name := checkDependencyGraphCmd)
  "#check_dependency_graph " str " against " str : command

elab_rules : command
  | `(#check_dependency_graph $theoremText:str against $payloadText:str) => do
      let theoremString := theoremText.getString
      let theoremName := theoremString.toName
      let expected ← match Json.parse payloadText.getString >>= fromJson? with
        | .ok value => pure (value : ExpectedGraph)
        | .error error => throwError m!"invalid dependency graph certificate JSON: {error}"
      if expected.theoremName != theoremString then
        throwError "command theorem name differs from embedded theoremName"
      if expected.topologySha256.length != 64 then
        throwError "embedded topologySha256 is not a SHA-256 digest"
      if expected.reconstructedProofSha256.length != 64 then
        throwError "embedded reconstructedProofSha256 is not a SHA-256 digest"
      let env ← getEnv
      let info ← match env.find? theoremName with
        | some (.thmInfo info) => pure info
        | some _ => throwError m!"{theoremName} is not a theorem"
        | none => throwError m!"theorem not found: {theoremName}"
      liftIO <| runMetaIO env do
        let actual ← analyzeTheorem info
        checkExpectedGraph expected actual
      let axioms ← Lean.collectAxioms theoremName
      if axioms.any (fun name => name == ``sorryAx || name.toString.toLower.contains "sorry") then
        throwError m!"{theoremName} depends on an incomplete proof axiom"
      logInfo m!"concrete dependency graph {expected.graphId}: checked {expected.edges.size} selected edge witnesses"

end DependencyGraphCertificate
