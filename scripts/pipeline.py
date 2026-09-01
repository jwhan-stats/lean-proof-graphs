#!/usr/bin/env python3
"""Build presentation-style dependency hypergraphs from Lean rollout JSONL.

The pipeline has deliberately separate evidence layers:

1. rollout provenance (tool calls and their paired results),
2. reconstructed Lean source (only accepted helpers + verified submission),
3. elaborated proof-term facts exported by ``graph_exporter``,
4. a compact manifest dependency hypergraph plus retrieval overlay,
5. an abstract selected-topology certificate, and
6. a self-contained concrete semantic certificate for every graph.

No semantic edge is inferred merely from chronology.  Chronology is retained
as provenance; proposition types and local-premise dependencies come from Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import math
import re
import subprocess
import sys
import textwrap
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterator, Sequence


EXPERIMENT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CONFIG = EXPERIMENT_ROOT / "config.json"
DEFAULT_OUTPUT = EXPERIMENT_ROOT / "outputs"
CONCRETE_SEMANTIC_CERTIFICATE_FILENAME = "semantic_graph_certificate.lean"
CONCRETE_SEMANTIC_CERTIFICATE_TEMPLATES = {
    "p1662_binary_quadratic_form_volume_identity": (
        EXPERIMENT_ROOT
        / "semantic_certificates"
        / "p1662_binary_quadratic_form_volume_identity.lean"
    ),
}
CONCRETE_SEMANTIC_CERTIFICATE_NAMESPACES = {
    "p1662_binary_quadratic_form_volume_identity": "P1662ConcreteSemanticGraph",
}
CONCRETE_SEMANTIC_DATA_VARIABLES = {
    "p1662_binary_quadratic_form_volume_identity": (
        ("a", "ℤ"), ("b", "ℤ"), ("c", "ℤ"),
        ("lam", "ℝ"), ("mu", "ℝ"),
    ),
}
CONCRETE_SEMANTIC_STATEMENT_REPLACEMENTS = {
    "p1662_binary_quadratic_form_volume_identity": (
        ("↑(-2 * a - b)", "((-2 * a - b : ℤ) : ℝ)"),
        ("↑(a + b + c)", "((a + b + c : ℤ) : ℝ)"),
        ("↑a", "(a : ℝ)"),
        ("↑b", "(b : ℝ)"),
        ("↑c", "(c : ℝ)"),
    ),
}


@dataclass
class ToolEvent:
    call_id: str
    name: str
    arguments: dict[str, Any]
    call_turn: int
    result_turn: int | None = None
    result: str = ""


@dataclass
class RetrievalEvent:
    event_id: str
    tool: str
    query: str
    declarations: list[str]
    call_turn: int
    result_turn: int | None


@dataclass
class Candidate:
    problem_idx: int
    unique_id: str
    source: str
    model: str
    token_count: int
    theorem_name: str
    formal_statement: str
    submission: str
    helpers: list[str]
    retrieval_events: list[RetrievalEvent]
    verification_call_id: str
    verification_result: str
    main_have_count: int
    accepted_helper_count: int
    tool_call_count: int
    source_file: str
    rejection_reasons: list[str] = field(default_factory=list)

    @property
    def slug(self) -> str:
        return f"p{self.problem_idx:04d}_{slugify(self.theorem_name, 42)}"

    @property
    def eligible(self) -> bool:
        return not self.rejection_reasons

    def summary(self) -> dict[str, Any]:
        data = {
            "problem_idx": self.problem_idx,
            "unique_id": self.unique_id,
            "source": self.source,
            "model": self.model,
            "token_count": self.token_count,
            "theorem_name": self.theorem_name,
            "slug": self.slug,
            "main_have_count": self.main_have_count,
            "accepted_helper_count": self.accepted_helper_count,
            "retrieval_event_count": len(self.retrieval_events),
            "tool_call_count": self.tool_call_count,
            "verification_call_id": self.verification_call_id,
            "source_file": self.source_file,
            "eligible": self.eligible,
            "rejection_reasons": self.rejection_reasons,
        }
        return data


def load_config(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def resolve_config_path(raw: str, config_path: Path) -> Path:
    path = Path(raw)
    return path if path.is_absolute() else (config_path.parent / path).resolve()


def portable_repo_path(path: Path) -> str:
    """Render a repository-local path without resolving local data symlinks."""

    absolute = path if path.is_absolute() else (EXPERIMENT_ROOT / path).absolute()
    try:
        return absolute.relative_to(EXPERIMENT_ROOT).as_posix()
    except ValueError:
        return absolute.as_posix()


def resolve_recorded_path(raw: str) -> Path:
    """Resolve a portable artifact path relative to the repository root."""

    path = Path(raw)
    return path if path.is_absolute() else (EXPERIMENT_ROOT / path).resolve()


def portable_json_value(value: Any) -> Any:
    """Remove this checkout's absolute root from persisted JSON evidence."""

    if isinstance(value, str):
        return value.replace(EXPERIMENT_ROOT.as_posix() + "/", "")
    if isinstance(value, list):
        return [portable_json_value(item) for item in value]
    if isinstance(value, dict):
        return {key: portable_json_value(item) for key, item in value.items()}
    return value


def iter_jsonl(path: Path) -> Iterator[dict[str, Any]]:
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
            if not isinstance(value, dict):
                raise ValueError(f"{path}:{line_no}: expected a JSON object")
            yield value


def slugify(value: str, limit: int = 64) -> str:
    value = re.sub(r"[^A-Za-z0-9_]+", "_", value).strip("_").lower()
    return (value or "unnamed")[:limit]


def strip_lean_comments_and_strings(source: str) -> str:
    """Remove nested comments and quoted strings before safety token checks."""

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        pair = source[i : i + 2]
        char = source[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                i += 2
            elif pair == "-/":
                block_depth -= 1
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            out.append("\n" if char == "\n" else " ")
            i += 1
            continue
        if pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
        elif pair == "--":
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif char == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(char)
            i += 1
    return "".join(out)


def forbidden_tokens(source: str, tokens: Sequence[str]) -> list[str]:
    clean = strip_lean_comments_and_strings(source)
    found = []
    for token in tokens:
        if re.search(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])", clean):
            found.append(token)
    return found


def pair_tool_events(conversation: Sequence[dict[str, Any]]) -> list[ToolEvent]:
    events: list[ToolEvent] = []
    by_id: dict[str, ToolEvent] = {}
    for turn, message in enumerate(conversation):
        for call in message.get("tool_calls") or []:
            event = ToolEvent(
                call_id=str(call.get("id", "")),
                name=str(call.get("name", "")),
                arguments=call.get("arguments") or {},
                call_turn=turn,
            )
            events.append(event)
            by_id[event.call_id] = event
        if message.get("role") == "tool":
            event = by_id.get(str(message.get("tool_call_id", "")))
            if event is not None:
                event.result_turn = turn
                event.result = str(message.get("content") or "")
    return events


def tool_passed(result: str) -> bool:
    return bool(
        re.search(r"### Compiles ###\s*True", result)
        and re.search(r"### Valid Proof ###\s*True", result)
    )


def helper_was_added(result: str) -> bool:
    return bool(re.search(r"### Added To File ###\s*True", result))


UNSOUND_WARNING_RE = re.compile(
    r"declaration uses [`']?(?:sorry|admit|axiom|sorryAx)", re.IGNORECASE
)


def parse_retrieved_declarations(result: str) -> list[str]:
    names: list[str] = []
    patterns = [
        re.compile(r"^\s*\d+\.\s+(?:\[\d+\]\s+)?([A-Za-z_][A-Za-z0-9_'.]*)", re.M),
        re.compile(r"^\s*[-*]\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*:", re.M),
    ]
    for pattern in patterns:
        names.extend(pattern.findall(result))
    return list(dict.fromkeys(names))


def extract_lean_fences(text: str) -> list[str]:
    return [match.group(1).strip() for match in re.finditer(
        r"```(?:lean|lean4)\s*\n(.*?)```", text, re.S | re.I
    )]


def extract_formal_statement(conversation: Sequence[dict[str, Any]]) -> str:
    for message in conversation:
        if message.get("role") != "user":
            continue
        content = str(message.get("content") or "")
        marker = content.find("### Formal Statement")
        if marker >= 0:
            fences = extract_lean_fences(content[marker:])
            if fences:
                return fences[0]
    return ""


THEOREM_RE = re.compile(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_'.]*)")
HELPER_DECL_RE = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def extract_candidate(
    record: dict[str, Any], source_path: Path, forbidden: Sequence[str]
) -> Candidate:
    metadata = record.get("metadata") or {}
    conversation = record.get("conversation") or []
    events = pair_tool_events(conversation)
    verification_events = [
        event for event in events
        if event.name == "verify_submission" and tool_passed(event.result)
    ]
    verification = verification_events[-1] if verification_events else None
    submission = ""
    if verification is not None:
        submission = str(verification.arguments.get("code") or "")
    theorem_match = THEOREM_RE.search(strip_lean_comments_and_strings(submission))
    theorem_name = theorem_match.group(1) if theorem_match else ""
    cutoff = verification.call_turn if verification is not None else math.inf
    accepted_helpers = [
        str(event.arguments.get("code") or "")
        for event in events
        if event.name == "add_to_file"
        and event.call_turn < cutoff
        and helper_was_added(event.result)
    ]
    retrieval_events = [
        RetrievalEvent(
            event_id=event.call_id,
            tool=event.name,
            query=str(event.arguments.get("query") or ""),
            declarations=parse_retrieved_declarations(event.result),
            call_turn=event.call_turn,
            result_turn=event.result_turn,
        )
        for event in events
        if event.name in {"loogle", "leanfinder"} and event.call_turn < cutoff
    ]
    clean_submission = strip_lean_comments_and_strings(submission)
    have_count = len(re.findall(r"(?m)^\s*(?:have|suffices)\b", clean_submission))
    rejections: list[str] = []
    if metadata.get("correct") is not True:
        rejections.append("metadata.correct is not true")
    if verification is None:
        rejections.append("no successful verify_submission")
    elif UNSOUND_WARNING_RE.search(verification.result):
        rejections.append("verify_submission reports an unsound placeholder")
    if not theorem_name:
        rejections.append("verified submission has no theorem declaration")
    combined = "\n\n".join([*accepted_helpers, submission])
    unsafe = forbidden_tokens(combined, forbidden)
    if unsafe:
        rejections.append("forbidden proof tokens: " + ", ".join(unsafe))
    return Candidate(
        problem_idx=int(metadata.get("problem_idx", -1)),
        unique_id=str(metadata.get("unique_id", "")),
        source=str(metadata.get("source", "")),
        model=str(metadata.get("model", "")),
        token_count=int(record.get("token_count") or 0),
        theorem_name=theorem_name,
        formal_statement=extract_formal_statement(conversation),
        submission=submission,
        helpers=accepted_helpers,
        retrieval_events=retrieval_events,
        verification_call_id=verification.call_id if verification else "",
        verification_result=verification.result if verification else "",
        main_have_count=have_count,
        accepted_helper_count=len(accepted_helpers),
        tool_call_count=len(events),
        source_file=str(source_path),
        rejection_reasons=rejections,
    )


def candidate_matches_policy(candidate: Candidate, policy: dict[str, Any]) -> bool:
    if not candidate.eligible:
        return False
    if not (int(policy["min_main_have_count"]) <= candidate.main_have_count
            <= int(policy["max_main_have_count"])):
        return False
    if len(candidate.submission) > int(policy["max_submission_chars"]):
        return False
    if policy.get("require_retrieval_event") and not candidate.retrieval_events:
        return False
    return True


def select_candidates(
    candidates: Sequence[Candidate], sample_size: int, policy: dict[str, Any]
) -> list[Candidate]:
    eligible = [item for item in candidates if candidate_matches_policy(item, policy)]
    strategy = str(policy.get("strategy") or "shortest_sound_structured_stratified_by_helpers")
    if strategy == "deterministic_hash_sample":
        seed = str(policy.get("seed") or "dependency-graph-default-seed")
        selected = sorted(
            eligible,
            key=lambda item: (candidate_hash_rank(item, seed), item.unique_id),
        )[:sample_size]
    elif strategy == "balanced_structural_round_robin":
        seed = str(policy.get("seed") or "dependency-graph-default-seed")
        buckets: dict[str, list[Candidate]] = defaultdict(list)
        for item in eligible:
            buckets[candidate_stratum(item, policy)].append(item)
        for values in buckets.values():
            values.sort(key=lambda item: (candidate_hash_rank(item, seed), item.unique_id))
        selected = []
        offsets = {name: 0 for name in buckets}
        while len(selected) < sample_size:
            progressed = False
            for name in sorted(buckets):
                offset = offsets[name]
                if offset < len(buckets[name]):
                    selected.append(buckets[name][offset])
                    offsets[name] += 1
                    progressed = True
                    if len(selected) == sample_size:
                        break
            if not progressed:
                break
    else:
        # Backward-compatible pilot policy.  It is useful for cheap smoke
        # testing, but its shortest-proof bias must not be used for corpus
        # distribution claims.
        eligible.sort(key=lambda item: (item.token_count, item.problem_idx))
        no_helpers = [item for item in eligible if item.accepted_helper_count == 0]
        with_helpers = [item for item in eligible if item.accepted_helper_count > 0]
        selected = no_helpers[: int(policy.get("no_helper_quota", 0))]
        selected += with_helpers[: int(policy.get("with_helper_quota", sample_size))]
        used = {item.unique_id for item in selected}
        if len(selected) < sample_size:
            selected.extend(item for item in eligible if item.unique_id not in used)
        selected = selected[:sample_size]
    if len(selected) != sample_size:
        raise RuntimeError(
            f"selection policy produced {len(selected)} candidates; expected {sample_size}"
        )
    return selected


def candidate_hash_rank(candidate: Candidate, seed: str) -> str:
    return hashlib.sha256(f"{seed}\0{candidate.unique_id}".encode()).hexdigest()


def numeric_bin(value: int, boundaries: Sequence[int]) -> str:
    lower = 0
    for upper in boundaries:
        if value <= upper:
            return f"{lower + 1}-{upper}"
        lower = upper
    return f"{lower + 1}+"


def candidate_stratum(candidate: Candidate, policy: dict[str, Any]) -> str:
    have_bins = [int(item) for item in policy.get("have_count_bin_maxima", [2, 5, 9, 18])]
    retrieval_bins = [
        int(item) for item in policy.get("retrieval_count_bin_maxima", [3, 8])
    ]
    helper = "no_helper" if candidate.accepted_helper_count == 0 else "with_helper"
    return "/".join([
        "have_" + numeric_bin(candidate.main_have_count, have_bins),
        helper,
        "retrieval_" + numeric_bin(len(candidate.retrieval_events), retrieval_bins),
    ])


def reconstructed_proof(candidate: Candidate) -> str:
    chunks = ["import Mathlib", ""]
    for index, helper in enumerate(candidate.helpers, 1):
        chunks.extend([
            f"/- accepted add_to_file helper {index} -/",
            helper.rstrip(),
            "",
        ])
    chunks.extend(["/- verified submission -/", candidate.submission.rstrip(), ""])
    return "\n".join(chunks)


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(portable_json_value(value), ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )


def normalize_json_tree(root: Path) -> None:
    """Make cached and freshly generated JSON artifacts checkout-portable."""

    for path in sorted(root.rglob("*.json")):
        write_json(path, json.loads(path.read_text(encoding="utf-8")))


def write_candidate_artifacts(candidate: Candidate, candidate_root: Path) -> dict[str, str]:
    out = candidate_root / candidate.slug
    out.mkdir(parents=True, exist_ok=True)
    proof_path = out / "proof.lean"
    proof_path.write_text(reconstructed_proof(candidate), encoding="utf-8")
    (out / "formal_statement.lean").write_text(
        candidate.formal_statement.rstrip() + "\n", encoding="utf-8"
    )
    write_json(out / "retrieval_events.json", [asdict(event) for event in candidate.retrieval_events])
    write_json(out / "record.json", candidate.summary())
    return {
        "slug": candidate.slug,
        "proof": str(proof_path),
        "raw_graph": str(out / "raw_graph.json"),
        "theorem_name": candidate.theorem_name,
        "batch_namespace": "Rollout_" + candidate.slug,
        "export_theorem_name": "Rollout_" + candidate.slug + "." + candidate.theorem_name,
    }


def without_import_commands(source: str) -> str:
    """Drop top-level imports when embedding a checked proof in a batch module."""

    return "\n".join(
        line for line in source.splitlines()
        if not re.match(r"^\s*import\b", line)
    ).strip()


def unclosed_command_scope_count(source: str) -> int:
    """Count file-local ``section``/``namespace`` scopes Lean closes at EOF.

    A standalone rollout may deliberately rely on EOF to close a scope, most
    commonly ``noncomputable section``.  Once that source is embedded inside a
    generated namespace, the EOF is no longer present and a following named
    ``end`` tries to close the rollout's unnamed section instead.  Comments and
    strings are blanked first so examples in prose do not affect the count.
    """

    depth = 0
    clean = strip_lean_comments_and_strings(source)
    for line_no, line in enumerate(clean.splitlines(), 1):
        if re.match(r"^\s*(?:noncomputable\s+)?section(?:\s|$)", line):
            depth += 1
        elif re.match(r"^\s*namespace(?:\s|$)", line):
            depth += 1
        elif re.match(r"^\s*end(?:\s|$)", line):
            depth -= 1
            if depth < 0:
                raise ValueError(
                    f"source closes a command scope it did not open at line {line_no}"
                )
    return depth


def write_batch_source(entries: Sequence[dict[str, str]], batch_dir: Path) -> Path:
    chunks = [
        "import Mathlib",
        "",
        "/- Generated only to amortize Mathlib loading during graph export. -/",
        "",
    ]
    for entry in entries:
        proof = Path(entry["proof"]).read_text(encoding="utf-8")
        embedded = without_import_commands(proof)
        eof_scope_count = unclosed_command_scope_count(embedded)
        chunks.extend([
            f"namespace {entry['batch_namespace']}",
            "",
            embedded,
            "",
            *(
                ["/- Scopes closed implicitly by EOF in the original file. -/"]
                + ["end"] * eof_scope_count
                + [""]
                if eof_scope_count
                else []
            ),
            f"end {entry['batch_namespace']}",
            "",
        ])
    batch_dir.mkdir(parents=True, exist_ok=True)
    path = batch_dir / "proofs.lean"
    path.write_text("\n".join(chunks).rstrip() + "\n", encoding="utf-8")
    return path


def split_batch_raw_graph(
    entries: Sequence[dict[str, str]], batch_raw_path: Path, batch_source_path: Path
) -> None:
    raw = portable_json_value(
        json.loads(batch_raw_path.read_text(encoding="utf-8"))
    )
    write_json(batch_raw_path, raw)
    for entry in entries:
        theorem_name = entry["export_theorem_name"]
        theorem_rows = [
            item for item in raw.get("theorems") or []
            if item.get("theorem_name") == theorem_name
        ]
        if len(theorem_rows) != 1:
            raise RuntimeError(
                f"batch exporter returned {len(theorem_rows)} rows for {theorem_name}"
            )
        local_edges = [
            item for item in raw.get("local_edges") or []
            if item.get("parent") == theorem_name
        ]
        excluded_local_bindings = [
            item for item in raw.get("excluded_local_bindings") or []
            if item.get("parent") == theorem_name
        ]
        sliced = {
            "schema_version": raw.get("schema_version"),
            "lean_version": raw.get("lean_version"),
            "theorems": theorem_rows,
            "local_edges": local_edges,
            "excluded_local_bindings": excluded_local_bindings,
            "diagnostics": raw.get("diagnostics") or [],
            "batch_provenance": {
                "source": str(batch_source_path),
                "namespace": entry["batch_namespace"],
                "isolation_mode": "generated_namespace_batch",
                "export_theorem_name": theorem_name,
                "proof_sha256": hashlib.sha256(
                    Path(entry["proof"]).read_bytes()
                ).hexdigest(),
            },
        }
        write_json(Path(entry["raw_graph"]), sliced)


def save_standalone_raw_graph(
    entry: dict[str, str], standalone_raw_path: Path, source_path: Path
) -> None:
    """Cache exporter output from the exact, unwrapped reconstructed source."""

    raw = portable_json_value(
        json.loads(standalone_raw_path.read_text(encoding="utf-8"))
    )
    theorem_names = [
        str(item.get("theorem_name") or "") for item in raw.get("theorems") or []
    ]
    if theorem_names != [entry["theorem_name"]]:
        raise RuntimeError(
            "standalone exporter returned unexpected theorem rows: "
            + repr(theorem_names)
        )
    raw["batch_provenance"] = {
        "source": str(source_path),
        "namespace": None,
        "isolation_mode": "standalone_source",
        "export_theorem_name": entry["theorem_name"],
        "proof_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
    }
    write_json(standalone_raw_path, raw)
    write_json(Path(entry["raw_graph"]), raw)


def raw_graph_cache_valid(entry: dict[str, str]) -> bool:
    path = Path(entry["raw_graph"])
    if not path.is_file():
        return False
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    if raw.get("schema_version") != "lean_proof_term_projection_raw_v4":
        return False
    if raw.get("lean_version") != "4.29.0":
        return False
    theorem_names = [str(item.get("theorem_name") or "") for item in raw.get("theorems") or []]
    allowed_names = {entry["export_theorem_name"], entry["theorem_name"]}
    if len(theorem_names) != 1 or theorem_names[0] not in allowed_names:
        return False
    provenance = raw.get("batch_provenance") or {}
    isolation_mode = provenance.get("isolation_mode")
    if isolation_mode not in {"generated_namespace_batch", "standalone_source"}:
        return False
    if provenance.get("export_theorem_name") != theorem_names[0]:
        return False
    if isolation_mode == "generated_namespace_batch" and not provenance.get("namespace"):
        return False
    if isolation_mode == "standalone_source" and provenance.get("namespace") is not None:
        return False
    source = resolve_recorded_path(str(provenance.get("source") or ""))
    if not source.is_file():
        return False
    recorded_hash = str(provenance.get("proof_sha256") or "")
    if recorded_hash:
        current_hash = hashlib.sha256(Path(entry["proof"]).read_bytes()).hexdigest()
        if recorded_hash != current_hash:
            return False
    return True


def batch_fingerprint(entries: Sequence[dict[str, str]]) -> str:
    digest = hashlib.sha256(b"dependency-graph-export-batch-v3\0")
    for entry in entries:
        digest.update(entry["export_theorem_name"].encode())
        digest.update(b"\0")
        digest.update(Path(entry["proof"]).read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()[:16]


def run_lean_exporter(
    entries: Sequence[dict[str, str]], output_root: Path, force: bool = False,
    batch_size: int = 20,
) -> None:
    executable = EXPERIMENT_ROOT / ".lake" / "build" / "bin" / "graph_exporter"
    if not executable.is_file():
        subprocess.run(["lake", "build", "graph_exporter"], cwd=EXPERIMENT_ROOT, check=True)
    pending = list(entries) if force else [entry for entry in entries if not raw_graph_cache_valid(entry)]
    reused = len(entries) - len(pending)
    print(f"[lean cache] reusing {reused}; exporting {len(pending)}", flush=True)
    if not pending:
        return
    if batch_size < 1:
        raise ValueError("Lean batch size must be positive")

    def export_batch(batch: Sequence[dict[str, str]]) -> None:
        batch_dir = output_root / "batches" / ("batch_" + batch_fingerprint(batch))
        batch_source = write_batch_source(batch, batch_dir)
        batch_raw = batch_dir / "raw_graph.json"
        print(
            f"[lean batch] elaborating {len(batch)} isolated rollout namespaces",
            flush=True,
        )
        command = [
            "lake", "env", str(executable), str(batch_source), str(batch_raw),
            *(entry["export_theorem_name"] for entry in batch),
        ]
        completed = subprocess.run(
            command,
            cwd=EXPERIMENT_ROOT,
            text=True,
            capture_output=True,
        )
        if completed.returncode == 0:
            split_batch_raw_graph(batch, batch_raw, batch_source)
            return
        diagnostic = "\n".join(
            part for part in (completed.stdout.strip(), completed.stderr.strip()) if part
        )[-4000:]
        if diagnostic:
            print("[lean batch diagnostic]\n" + diagnostic, flush=True)
        if len(batch) == 1:
            entry = batch[0]
            standalone_dir = output_root / "standalone" / entry["slug"]
            standalone_dir.mkdir(parents=True, exist_ok=True)
            standalone_raw = standalone_dir / "raw_graph.json"
            standalone_source = Path(entry["proof"])
            print(
                "[lean fallback] retrying exact standalone source for "
                + entry["theorem_name"],
                flush=True,
            )
            fallback = subprocess.run(
                [
                    "lake", "env", str(executable), str(standalone_source),
                    str(standalone_raw), entry["theorem_name"],
                ],
                cwd=EXPERIMENT_ROOT,
                text=True,
                capture_output=True,
            )
            fallback_diagnostic = "\n".join(
                part for part in (fallback.stdout.strip(), fallback.stderr.strip()) if part
            )[-4000:]
            if fallback.returncode == 0:
                save_standalone_raw_graph(entry, standalone_raw, standalone_source)
                return
            raise RuntimeError(
                "Lean graph export failed in both namespaced and standalone modes for "
                + entry["theorem_name"]
                + "\n[namespaced]\n"
                + diagnostic
                + "\n[standalone]\n"
                + fallback_diagnostic
            )
        # A bad reconstruction should not hide all other members of a large
        # cohort.  Bisect deterministically until the failing item is named.
        midpoint = len(batch) // 2
        print(
            f"[lean batch] failed; bisecting into {midpoint} and {len(batch) - midpoint}",
            flush=True,
        )
        export_batch(batch[:midpoint])
        export_batch(batch[midpoint:])

    for start in range(0, len(pending), batch_size):
        export_batch(pending[start : start + batch_size])


def normalize_statement(statement: str) -> str:
    return re.sub(r"\s+", " ", statement).strip()


def proposition_record(prop: dict[str, Any]) -> dict[str, str]:
    """Canonical, auditable identity for one Lean proposition binding."""

    return {
        "fvar_id": str(prop.get("fvar_id") or prop.get("lean_fvar_id") or ""),
        "name": str(prop.get("name") or prop.get("binding_name") or ""),
        "statement": normalize_statement(str(prop.get("statement") or "")),
    }


def raw_dependency_record(raw_edge: dict[str, Any]) -> dict[str, Any]:
    return {
        "premises": [proposition_record(item) for item in raw_edge.get("premises") or []],
        "conclusion": proposition_record(raw_edge.get("conclusion") or {}),
    }


def dependency_record_fingerprint(record: dict[str, Any]) -> str:
    encoded = json.dumps(
        record, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def info_tree_exclusion_audit(raw: dict[str, Any]) -> dict[str, Any]:
    """Summarize transient target bindings that were not sound graph edges."""

    excluded = list(raw.get("excluded_local_bindings") or [])
    return {
        "count": len(excluded),
        "reason_counts": dict(sorted(Counter(
            str(item.get("reason") or "unspecified") for item in excluded
        ).items())),
        "policy": "not_emitted_as_dependency_edge",
    }


def classify_axioms(axioms: Sequence[str]) -> dict[str, Any]:
    names = sorted(dict.fromkeys(str(item) for item in axioms))
    incomplete = [
        name for name in names
        if name == "sorryAx" or name.endswith(".sorryAx") or "sorry" in name.lower()
    ]
    classical = [name for name in names if name == "Classical.choice"]
    extensional_or_quotient = [
        name for name in names if name in {"propext", "Quot.sound"}
    ]
    other = [
        name for name in names
        if name not in set(incomplete + classical + extensional_or_quotient)
    ]
    return {
        "axioms": names,
        "constructive_core_only": not names,
        "classical": classical,
        "extensional_or_quotient": extensional_or_quotient,
        "incomplete_or_unsafe": incomplete,
        "other": other,
        "status": "passed" if not incomplete else "failed",
    }


def source_mentions(source: str, name: str) -> bool:
    simple = name.rsplit(".", 1)[-1]
    return bool(re.search(rf"(?<![A-Za-z0-9_'.])(?:{re.escape(name)}|{re.escape(simple)})(?![A-Za-z0-9_'])", source))


TACTIC_LABELS = (
    "omega", "linarith", "nlinarith", "norm_num", "positivity", "ring_nf",
    "ring", "aesop", "grind", "simp_all", "simpa", "simp", "tauto",
    "constructor", "ext", "exact", "apply", "refine", "rw",
)


def infer_tactic_labels(fragment: str) -> list[str]:
    clean = strip_lean_comments_and_strings(fragment)
    labels = [name for name in TACTIC_LABELS if re.search(rf"\b{re.escape(name)}\b", clean)]
    return labels[:3] or ["proof_term_composition"]


def binding_fragment(source: str, binding_name: str, limit: int = 1200) -> str:
    lines = source.splitlines()
    pattern = re.compile(rf"^([ \t]*)(?:have|suffices)\s+{re.escape(binding_name)}\b")
    for index, line in enumerate(lines):
        match = pattern.search(line)
        if not match:
            continue
        indent = len(match.group(1).replace("\t", "  "))
        block = [line]
        for following in lines[index + 1 :]:
            if following.strip():
                current = len(following) - len(following.lstrip(" "))
                if current <= indent and re.match(r"\s*(?:have|suffices|exact|apply|refine|simpa|constructor|by_cases|rcases|obtain)\b", following):
                    break
            block.append(following)
        return "\n".join(block)[:limit]
    return ""


def final_fragment(source: str, limit: int = 1600) -> str:
    marker = source.find(":= by")
    body = source[marker + 5 :] if marker >= 0 else source
    lines = body.splitlines()
    candidates = [
        index for index, line in enumerate(lines)
        if re.match(r"^\s{2}(?:exact|simpa|apply|refine|constructor|aesop|omega|linarith|nlinarith|grind)\b", line)
    ]
    start = candidates[-1] if candidates else max(0, len(lines) - 20)
    return "\n".join(lines[start:])[:limit]


def retrieval_index(events: Sequence[RetrievalEvent]) -> dict[str, list[str]]:
    index: dict[str, list[str]] = defaultdict(list)
    for event in events:
        for declaration in event.declarations:
            index[declaration].append(event.event_id)
            index[declaration.rsplit(".", 1)[-1]].append(event.event_id)
    return index


def helper_declaration_names(candidate: Candidate) -> set[str]:
    return {
        match
        for helper in candidate.helpers
        for match in HELPER_DECL_RE.findall(strip_lean_comments_and_strings(helper))
    }


def compact_rule_items(
    raw_items: Sequence[str], fragment: str, events: Sequence[RetrievalEvent]
) -> list[str]:
    retrieval_names = {
        name for event in events for name in event.declarations
    }
    kept: list[str] = []
    for name in raw_items:
        if name.startswith(("Mathlib.Meta.", "Lean.Meta.")):
            continue
        simple = name.rsplit(".", 1)[-1]
        if simple.startswith("inst") or ".inst" in name:
            continue
        if source_mentions(fragment, name) or name in retrieval_names or simple in {
            item.rsplit(".", 1)[-1] for item in retrieval_names
        }:
            kept.append(name)
    return list(dict.fromkeys(kept))[:8]


def node_key(name: str, statement: str, fvar_id: str = "") -> tuple[str, str]:
    if fvar_id:
        return ("lean_fvar", fvar_id)
    return (name, normalize_statement(statement))


def stable_node_id(name: str, statement: str, origin: str, fvar_id: str = "") -> str:
    if origin == "goal":
        return "n_goal"
    prefix = "m" if origin.startswith("manifest") else "n"
    identity = f"{fvar_id}\0{normalize_statement(statement)}" if fvar_id else normalize_statement(statement)
    digest = hashlib.sha256(identity.encode()).hexdigest()[:8]
    return f"{prefix}_{slugify(name, 24)}_{digest}"


SIDE_PATTERNS = re.compile(r"\b(?:Nonempty|BddAbove|Decidable|Finite|Fintype|NeZero|NoZeroSMulDivisors)\b")


def project_graph(
    candidate: Candidate,
    raw: dict[str, Any],
    proof_rel: str,
    raw_rel: str,
    export_theorem_name: str,
) -> dict[str, Any]:
    theorem_rows = raw.get("theorems") or []
    theorem = next(
        (item for item in theorem_rows if item.get("theorem_name") == export_theorem_name),
        None,
    )
    if theorem is None:
        raise ValueError(f"raw graph has no theorem {export_theorem_name}")

    raw_edges = list(theorem.get("local_edges") or [])
    if not raw_edges:
        raw_edges = [
            item for item in raw.get("local_edges") or []
            if item.get("parent") == export_theorem_name
        ]
    raw_edges.append(theorem["final_edge"])
    nodes: dict[tuple[str, str], dict[str, Any]] = {}

    def ensure_node(prop: dict[str, Any], forced_origin: str | None = None) -> str:
        name = str(prop.get("name") or "anonymous")
        statement = normalize_statement(str(prop.get("statement") or ""))
        fvar_id = str(prop.get("fvar_id") or "")
        key = node_key(name, statement, fvar_id)
        origin = forced_origin or str(prop.get("origin") or "local_assumption")
        existing = nodes.get(key)
        if existing is not None:
            if origin == "manifest":
                existing["origin"] = "manifest"
                existing["class"] = "main"
            return existing["id"]
        node_class = "side" if origin != "manifest" and SIDE_PATTERNS.search(statement) else "main"
        node = {
            "id": stable_node_id(name, statement, origin, fvar_id),
            "class": node_class,
            "origin": origin,
            "selected": False,
            "binding_name": name,
            "lean_fvar_id": fvar_id or None,
            "statement": statement,
        }
        nodes[key] = node
        return node["id"]

    for prop in theorem.get("manifest") or []:
        ensure_node(prop, "manifest")
    goal_id = ensure_node(theorem["goal"], "goal")
    rindex = retrieval_index(candidate.retrieval_events)
    helper_names = helper_declaration_names(candidate)
    hyperedges: list[dict[str, Any]] = []
    seen_edges: set[tuple[Any, ...]] = set()
    for ordinal, raw_edge in enumerate(raw_edges, 1):
        witness_check = raw_edge.get("witness_check") or {}
        if not (
            witness_check.get("kernel_typecheck") is True
            and witness_check.get("conclusion_defeq_proof_type") is True
            and witness_check.get("contains_unresolved_metavariables") is False
        ):
            raise ValueError(
                f"raw edge {raw_edge.get('id')} lacks a passing Lean witness check"
            )
        dependency_record = raw_dependency_record(raw_edge)
        conclusion_prop = raw_edge["conclusion"]
        is_goal = raw_edge.get("id") == "goal_edge"
        conclusion = goal_id if is_goal else ensure_node(conclusion_prop, "derived")
        premises = [ensure_node(prop) for prop in raw_edge.get("premises") or []]
        conclusion_name = str(conclusion_prop.get("name") or "")
        fragment = final_fragment(candidate.submission) if is_goal else binding_fragment(
            candidate.submission, conclusion_name
        )
        if not fragment:
            for helper in candidate.helpers:
                fragment = binding_fragment(helper, conclusion_name)
                if fragment:
                    break
        rule_items = compact_rule_items(raw_edge.get("rule_items") or [], fragment, candidate.retrieval_events)
        helper_items = [
            item for item in rule_items
            if item.rsplit(".", 1)[-1] in helper_names
        ]
        mathlib_items = [item for item in rule_items if item not in helper_items]
        display_items = [
            item.rsplit(".", 1)[-1] if item in helper_items else item
            for item in rule_items
        ]
        labels = display_items or infer_tactic_labels(fragment)
        event_ids = list(dict.fromkeys(
            event_id
            for item in rule_items
            for event_id in (rindex.get(item, []) + rindex.get(item.rsplit(".", 1)[-1], []))
        ))
        matched_rule_items = [
            item for item in rule_items
            if rindex.get(item) or rindex.get(item.rsplit(".", 1)[-1])
        ]
        signature = (tuple(premises), conclusion, tuple(labels))
        if signature in seen_edges:
            continue
        seen_edges.add(signature)
        edge_id = "h_goal" if is_goal else f"h_{ordinal:03d}_{slugify(conclusion_name, 24)}"
        edge_class = "side" if next(node for node in nodes.values() if node["id"] == conclusion)["class"] == "side" else "main"
        hyperedges.append({
            "id": edge_id,
            "class": edge_class,
            "selected": False,
            "premises": premises,
            "conclusion": conclusion,
            "rule": {
                "kind": (
                    "named_declaration_composition" if helper_items and mathlib_items
                    else "rollout_helper_declaration" if helper_items
                    else "mathlib_declaration" if mathlib_items
                    else "tactic_or_logical_construction"
                ),
                "label": " + ".join(labels[:3]),
                "items": rule_items,
                "rollout_helper_items": helper_items,
                "mathlib_items": mathlib_items,
            },
            "provenance": {
                "raw_edge_id": raw_edge.get("id"),
                "source": raw_edge.get("source"),
                "proof_fragment": fragment,
                "lean_dependency_record": dependency_record,
                "lean_dependency_sha256": dependency_record_fingerprint(dependency_record),
                "kernel_witness_check": witness_check,
            },
            "retrieval": {
                "matched_rule_items": matched_rule_items,
                "observed_search_event_ids": event_ids,
                "direct_search_observed": bool(event_ids),
            },
        })

    node_by_id = {node["id"]: node for node in nodes.values()}
    by_conclusion: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in hyperedges:
        by_conclusion[edge["conclusion"]].append(edge)
    selected_nodes: set[str] = set()
    selected_edges: set[str] = set()
    agenda = [goal_id]
    while agenda:
        current = agenda.pop()
        if current in selected_nodes:
            continue
        selected_nodes.add(current)
        incoming = by_conclusion.get(current, [])
        if incoming:
            edge = incoming[-1]
            selected_edges.add(edge["id"])
            agenda.extend(edge["premises"])
    for node_id in selected_nodes:
        node_by_id[node_id]["selected"] = True
    for edge in hyperedges:
        edge["selected"] = edge["id"] in selected_edges

    integrity = validate_and_measure(node_by_id, hyperedges, goal_id)
    matched_events = {
        event_id
        for edge in hyperedges if edge["selected"]
        for event_id in edge["retrieval"]["observed_search_event_ids"]
    }
    axiom_audit = classify_axioms(theorem.get("axioms") or [])
    exclusion_audit = info_tree_exclusion_audit(raw)
    graph = {
        "schema_version": "manifest_dependency_hypergraph_v2",
        "graph_id": candidate.slug,
        "task": {
            "benchmark": "math__arxivlean_trajectories",
            "problem_idx": candidate.problem_idx,
            "source": candidate.source,
            "theorem_name": candidate.theorem_name,
            "goal_node": goal_id,
        },
        "sources": {
            "rollout_jsonl": candidate.source_file,
            "rollout_unique_id": candidate.unique_id,
            "reconstructed_proof": proof_rel,
            "raw_elaboration": raw_rel,
            "batch_export_theorem_name": export_theorem_name,
            "verification_call_id": candidate.verification_call_id,
        },
        "projection": {
            "method": "automatic_from_elaborated_proposition_bindings",
            "status": "pilot_candidate",
            "minimality_status": "selected_derivation_only",
            "graph_semantics": "forward_manifest_dependency_hypergraph",
            "node_unit": "elaborated proposition binding; theorem-value telescope preferred, target InfoTree fallback",
            "edge_unit": "metavariable-free proof value checked by Lean's kernel in its local context",
            "excluded_info_tree_bindings": exclusion_audit,
            "policies": {
                "universal_introduction": "fixed at graph boundary; not an edge",
                "named_mathlib_declaration": "atomic",
                "accepted_rollout_helper": "atomic and separately tagged",
                "binding_identity": "Lean FVarId within the theorem-value telescope",
                "duplicate_propositions": "distinct binders remain distinct even when propositions print identically",
                "side_conditions": "retained and tagged; excluded from main-only metrics",
                "retrieval": "declaration-name overlay; search events are not reasoning nodes",
                "incomplete_info_tree_snapshot": "audited and excluded; never emitted as a verified edge",
            },
        },
        "nodes": sorted(nodes.values(), key=lambda item: item["id"]),
        "hyperedges": hyperedges,
        "retrieval_events": [asdict(event) for event in candidate.retrieval_events],
        "axiom_audit": axiom_audit,
        "metrics": {
            **integrity["metrics"],
            "retrieval_query_count": len(candidate.retrieval_events),
            "useful_retrieval_event_count": len(matched_events),
            "unused_retrieval_event_count": len(candidate.retrieval_events) - len(matched_events),
            "accepted_helper_count": candidate.accepted_helper_count,
            "rollout_tool_call_count": candidate.tool_call_count,
            "excluded_info_tree_binding_count": exclusion_audit["count"],
        },
        "validation": {
            "metadata_correct": True,
            "recorded_verify_submission": "passed",
            "unsafe_placeholder_gate": "passed",
            "reconstructed_lean_4_29_elaboration": "passed_in_isolated_namespace_batch",
            "edge_witnesses_from_elaborated_terms": "kernel_typechecked_in_original_local_context",
            "incomplete_info_tree_snapshots": (
                "none"
                if exclusion_audit["count"] == 0
                else f"{exclusion_audit['count']}_audited_and_excluded"
            ),
            "projection_dependency_fingerprints": "passed",
            "lean_topology_certificate": "pending",
            "lean_concrete_semantic_certificate": "not_emitted",
            "standalone_source_level_semantic_edge_replay": "not_emitted",
            "axiom_audit": axiom_audit["status"],
            "acyclic": integrity["acyclic"],
            "goal_reachable": integrity["goal_reachable"],
            "unresolved_selected_derived_nodes": integrity["unresolved"],
        },
    }
    return graph


def validate_and_measure(
    nodes: dict[str, dict[str, Any]], edges: Sequence[dict[str, Any]], goal: str
) -> dict[str, Any]:
    selected_edges = [edge for edge in edges if edge.get("selected")]
    incoming = {edge["conclusion"]: edge for edge in selected_edges}
    visiting: set[str] = set()
    memo: dict[str, int] = {}
    unresolved: list[str] = []
    acyclic = True

    def depth(node_id: str) -> int:
        nonlocal acyclic
        if node_id in memo:
            return memo[node_id]
        if node_id in visiting:
            acyclic = False
            return 0
        node = nodes[node_id]
        if node["origin"] in {"manifest", "local_assumption", "ambient_instance"}:
            memo[node_id] = 0
            return 0
        edge = incoming.get(node_id)
        if edge is None:
            unresolved.append(node_id)
            memo[node_id] = 0
            return 0
        visiting.add(node_id)
        value = 1 + max((depth(p) for p in edge["premises"]), default=0)
        visiting.remove(node_id)
        memo[node_id] = value
        return value

    goal_depth = depth(goal)
    selected_nodes = {goal}
    for edge in selected_edges:
        selected_nodes.add(edge["conclusion"])
        selected_nodes.update(edge["premises"])
    main_edges = [edge for edge in selected_edges if edge["class"] == "main"]
    metrics = {
        "selected_node_count": len(selected_nodes),
        "selected_hyperedge_count": len(selected_edges),
        "main_hyperedge_count": len(main_edges),
        "side_hyperedge_count": len(selected_edges) - len(main_edges),
        "selected_depth": goal_depth,
        "max_fan_in_all": max((len(edge["premises"]) for edge in selected_edges), default=0),
        "max_fan_in_main": max((len([p for p in edge["premises"] if nodes[p]["class"] == "main"]) for edge in main_edges), default=0),
        "manifest_fact_count": sum(nodes[node_id]["origin"] == "manifest" for node_id in selected_nodes),
        "retrieved_rule_item_count": len({
            item for edge in selected_edges for item in edge["retrieval"]["matched_rule_items"]
        }),
    }
    return {
        "acyclic": acyclic,
        "goal_reachable": goal in memo and not unresolved and acyclic,
        "unresolved": sorted(set(unresolved)),
        "depths": memo,
        "metrics": metrics,
    }


def graph_layers(graph: dict[str, Any]) -> dict[str, int]:
    nodes = {item["id"]: item for item in graph["nodes"] if item.get("selected")}
    edges = [item for item in graph["hyperedges"] if item.get("selected")]
    incoming = {edge["conclusion"]: edge for edge in edges}
    memo: dict[str, int] = {}

    def depth(node_id: str) -> int:
        if node_id in memo:
            return memo[node_id]
        node = nodes[node_id]
        if node["origin"] in {"manifest", "local_assumption", "ambient_instance"}:
            memo[node_id] = 0
        elif node_id not in incoming:
            memo[node_id] = 0
        else:
            memo[node_id] = 1 + max((depth(p) for p in incoming[node_id]["premises"]), default=0)
        return memo[node_id]

    for node_id in nodes:
        depth(node_id)
    return memo


def selected_topological_edges(graph: dict[str, Any]) -> tuple[list[str], list[dict[str, Any]]]:
    selected_nodes = {
        item["id"]: item for item in graph["nodes"] if item.get("selected")
    }
    selected_edges = [
        item for item in graph["hyperedges"] if item.get("selected")
    ]
    produced = {edge["conclusion"] for edge in selected_edges}
    boundary = sorted(set(selected_nodes) - produced)
    known = set(boundary)
    pending = sorted(selected_edges, key=lambda item: item["id"])
    ordered: list[dict[str, Any]] = []
    while pending:
        ready = [
            edge for edge in pending
            if set(edge.get("premises") or []).issubset(known)
        ]
        if not ready:
            raise ValueError("selected graph cannot be topologically composed")
        for edge in ready:
            ordered.append(edge)
            known.add(edge["conclusion"])
            pending.remove(edge)
    goal = graph["task"]["goal_node"]
    if goal not in known:
        raise ValueError("topological composition does not derive the goal")
    return boundary, ordered


def topology_payload(graph: dict[str, Any]) -> dict[str, Any]:
    boundary, ordered = selected_topological_edges(graph)
    nodes = {item["id"]: item for item in graph["nodes"] if item.get("selected")}
    node_order = list(boundary)
    for edge in ordered:
        if edge["conclusion"] not in node_order:
            node_order.append(edge["conclusion"])
    node_order.extend(node_id for node_id in sorted(nodes) if node_id not in node_order)
    return {
        "graph_id": graph["graph_id"],
        "goal": graph["task"]["goal_node"],
        "nodes": [{
            "id": node_id,
            "binding_name": nodes[node_id]["binding_name"],
            "statement": nodes[node_id]["statement"],
        } for node_id in node_order],
        "boundary": boundary,
        "edges": [{
            "id": edge["id"],
            "premises": edge["premises"],
            "conclusion": edge["conclusion"],
        } for edge in ordered],
    }


def topology_fingerprint(graph: dict[str, Any]) -> str:
    encoded = json.dumps(
        topology_payload(graph), ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode()
    return hashlib.sha256(encoded).hexdigest()


def safe_lean_comment(value: str) -> str:
    return value.replace("-/", "- / ").replace("\r", " ")


def topology_certificate_source(graph: dict[str, Any], include_import: bool = True) -> str:
    """Emit a small Lean proof of the selected graph's topology.

    The node propositions are abstract atoms here.  Their semantic witnesses
    are checked separately by ``GraphExporter.lean`` in the original local
    contexts.  This certificate checks the second half of the contract: that
    the exact selected hyperedges compose from boundary facts to the goal.
    """

    payload = topology_payload(graph)
    node_ids = [item["id"] for item in payload["nodes"]]
    node_names = {node_id: f"N{index:03d}" for index, node_id in enumerate(node_ids, 1)}
    boundary_names = {
        node_id: f"B{index:03d}" for index, node_id in enumerate(payload["boundary"], 1)
    }
    edge_names = {
        edge["id"]: f"E{index:03d}" for index, edge in enumerate(payload["edges"], 1)
    }
    namespace = "TopologyCertificate_" + slugify(graph["graph_id"], 72)
    lines: list[str] = []
    if include_import:
        lines.extend(["import Init", ""])
    lines.extend([
        "/- Generated dependency-topology certificate.",
        "Semantic edge witnesses are kernel-checked in the reconstructed proof;",
        "this theorem independently checks composition of the selected closure. -/",
        f"-- graph_id: {safe_lean_comment(graph['graph_id'])}",
        f"-- topology_sha256: {topology_fingerprint(graph)}",
        f"namespace {namespace}",
        "",
    ])
    payload_nodes = {item["id"]: item for item in payload["nodes"]}
    for node_id in node_ids:
        node = payload_nodes[node_id]
        lines.append(
            f"-- {node_names[node_id]} = {safe_lean_comment(node['binding_name'])}: "
            f"{safe_lean_comment(node['statement'])}"
        )
    lines.append("")
    for edge in payload["edges"]:
        lines.append(f"-- {edge_names[edge['id']]} represents {safe_lean_comment(edge['id'])}")
    lines.extend(["", "theorem graph_derives_goal"])
    for node_id in node_ids:
        lines.append(f"    ({node_names[node_id]} : Prop)")
    for node_id in payload["boundary"]:
        lines.append(
            f"    ({boundary_names[node_id]} : {node_names[node_id]})"
        )
    for edge in payload["edges"]:
        premise_types = [node_names[item] for item in edge["premises"]]
        edge_type = " → ".join([*premise_types, node_names[edge["conclusion"]]])
        lines.append(f"    ({edge_names[edge['id']]} : {edge_type})")
    lines.append(f"    : {node_names[payload['goal']]} := by")
    proofs = dict(boundary_names)
    for edge in payload["edges"]:
        conclusion = edge["conclusion"]
        proof_name = "H_" + node_names[conclusion]
        application = " ".join([
            edge_names[edge["id"]],
            *(proofs[item] for item in edge["premises"]),
        ])
        lines.append(f"  have {proof_name} : {node_names[conclusion]} := {application}")
        proofs[conclusion] = proof_name
    lines.extend([
        f"  exact {proofs[payload['goal']]}",
        "",
        f"end {namespace}",
        "",
    ])
    return "\n".join(lines)


def write_topology_certificates(
    graphs: Sequence[dict[str, Any]], graph_root: Path, output_root: Path
) -> Path:
    certificate_root = output_root / "certificates"
    certificate_root.mkdir(parents=True, exist_ok=True)
    for graph in graphs:
        path = graph_root / graph["graph_id"] / "topology_certificate.lean"
        source = topology_certificate_source(graph, include_import=True)
        path.write_text(source, encoding="utf-8")
        graph["sources"]["topology_certificate"] = "topology_certificate.lean"
        graph["sources"]["topology_sha256"] = topology_fingerprint(graph)
    batch_path = certificate_root / "topology_certificates.lean"
    batch_path.write_text(topology_batch_source(graphs), encoding="utf-8")
    return batch_path


def topology_batch_source(graphs: Sequence[dict[str, Any]]) -> str:
    combined = [
        "import Init",
        "",
        "/- Generated batch: one abstract topology theorem per selected graph. -/",
        "",
    ]
    for graph in sorted(graphs, key=lambda item: item["graph_id"]):
        combined.append(topology_certificate_source(graph, include_import=False))
    return "\n".join(combined)


def run_topology_lean_check(
    graphs: Sequence[dict[str, Any]], batch_path: Path, output_root: Path,
    quiet: bool = False,
) -> dict[str, Any]:
    completed = subprocess.run(
        ["lake", "env", "lean", str(batch_path)],
        cwd=EXPERIMENT_ROOT,
        text=True,
        capture_output=True,
    )
    report = {
        "schema_version": "lean_topology_certificate_report_v1",
        "status": "passed" if completed.returncode == 0 else "failed",
        "graph_count": len(graphs),
        "batch_source": str(batch_path),
        "batch_sha256": hashlib.sha256(batch_path.read_bytes()).hexdigest(),
        "returncode": completed.returncode,
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    }
    write_json(output_root / "topology_validation.json", report)
    if completed.returncode != 0:
        diagnostic = completed.stderr or completed.stdout
        raise RuntimeError("Lean topology-certificate batch failed: " + diagnostic[-2000:])
    for graph in graphs:
        graph["validation"]["lean_topology_certificate"] = "passed_in_fresh_lean_process"
    if not quiet:
        print(f"Lean checked {len(graphs)} topology certificates")
    return report


def certificate_metadata_values(source: str, key: str) -> list[str]:
    return re.findall(
        rf"^-- {re.escape(key)}:\s*(\S+)\s*$", source, flags=re.MULTILINE
    )


def concrete_graph_statement_source(graph_id: str, statement: str) -> str:
    """Disambiguate pretty-printed coercions using the certificate's data context."""

    result = statement
    for old, new in CONCRETE_SEMANTIC_STATEMENT_REPLACEMENTS[graph_id]:
        result = result.replace(old, new)
    if "↑" in result:
        raise ValueError(
            f"unresolved pretty-printed coercion in {graph_id}: {statement}"
        )
    return result


def concrete_semantic_type_bridge_source(graph: dict[str, Any]) -> str:
    """Generate Lean examples equating reviewed edge types with graph.json types."""

    graph_id = str(graph["graph_id"])
    namespace = CONCRETE_SEMANTIC_CERTIFICATE_NAMESPACES[graph_id]
    variables = CONCRETE_SEMANTIC_DATA_VARIABLES[graph_id]
    nodes = {str(node["id"]): node for node in graph["nodes"]}
    _, ordered_edges = selected_topological_edges(graph)
    lines = [
        "/- Generated exact graph/type bridge. Do not edit this section.",
        "Each example applies the reviewed concrete edge theorem to precisely",
        "the premise and conclusion propositions rendered in graph.json. -/",
        f"-- generated_bridge_topology_sha256: {topology_fingerprint(graph)}",
        f"namespace ConcreteGraphTypeBridge_{slugify(graph_id, 72)}",
        "",
    ]
    grouped: dict[str, list[str]] = defaultdict(list)
    for name, lean_type in variables:
        grouped[lean_type].append(name)
    for lean_type, names in grouped.items():
        lines.append(f"variable ({' '.join(names)} : {lean_type})")
    lines.append("")

    for edge in ordered_edges:
        edge_id = str(edge["id"])
        proposition_sources = [
            concrete_graph_statement_source(
                graph_id, str(nodes[str(node_id)]["statement"])
            )
            for node_id in [*(edge.get("premises") or []), edge["conclusion"]]
        ]
        premise_sources = proposition_sources[:-1]
        conclusion_source = proposition_sources[-1]
        combined = "\n".join(proposition_sources)
        data_arguments = [
            f"({name} := {name})"
            for name, _ in variables
            if re.search(rf"\b{re.escape(name)}\b", combined)
        ]
        premise_arguments = [f"P{index:03d}" for index in range(1, len(premise_sources) + 1)]
        application = " ".join([
            f"{namespace}.edge_{edge_id}",
            *data_arguments,
            *premise_arguments,
        ])
        lines.append(f"-- graph edge: {edge_id}")
        lines.append("example")
        for index, premise_source in enumerate(premise_sources, 1):
            lines.append(f"    (P{index:03d} : {premise_source})")
        lines.extend([
            f"    : {conclusion_source} := by",
            f"  exact {application}",
            "",
        ])
    lines.extend([
        f"end ConcreteGraphTypeBridge_{slugify(graph_id, 72)}",
        "",
    ])
    return "\n".join(lines)


def reviewed_concrete_semantic_certificate_source(graph: dict[str, Any]) -> str:
    template_path = CONCRETE_SEMANTIC_CERTIFICATE_TEMPLATES[str(graph["graph_id"])]
    template = template_path.read_text(encoding="utf-8").rstrip()
    return template + "\n\n" + concrete_semantic_type_bridge_source(graph)


def concrete_semantic_certificate_kind(graph: dict[str, Any]) -> str:
    if str(graph["graph_id"]) in CONCRETE_SEMANTIC_CERTIFICATE_TEMPLATES:
        return "reviewed_edge_theorems"
    return "embedded_theorem_replay"


def concrete_semantic_replay_spec(
    graph: dict[str, Any], reconstructed_proof: Path
) -> dict[str, Any]:
    """Build the manifest consumed by GraphCertificate's Lean command."""

    selected_nodes = [node for node in graph["nodes"] if node.get("selected")]
    identities = [
        (str(node["binding_name"]), normalize_statement(str(node["statement"])))
        for node in selected_nodes
    ]
    if len(identities) != len(set(identities)):
        raise ValueError(
            f"{graph['graph_id']}: generic semantic replay requires unique "
            "selected (binding name, proposition) identities"
        )

    def prop_record(value: dict[str, Any]) -> dict[str, str]:
        name = str(value.get("name") or "")
        if name.startswith("inst._@"):
            name = "<generated-instance>"
        elif "._@._internal." in name:
            name = "<generated-internal>"
        return {
            "name": name,
            "statement": normalize_statement(str(value.get("statement") or "")),
        }

    _, ordered_edges = selected_topological_edges(graph)
    edges = []
    for edge in ordered_edges:
        provenance = edge.get("provenance") or {}
        dependency = provenance.get("lean_dependency_record") or {}
        edges.append({
            "graphEdgeId": str(edge["id"]),
            "rawEdgeId": str(provenance.get("raw_edge_id") or ""),
            "premises": [
                prop_record(item) for item in dependency.get("premises") or []
            ],
            "conclusion": prop_record(dependency.get("conclusion") or {}),
        })
    return {
        "graphId": str(graph["graph_id"]),
        "theoremName": str(graph["task"]["theorem_name"]),
        "topologySha256": topology_fingerprint(graph),
        "reconstructedProofSha256": hashlib.sha256(
            reconstructed_proof.read_bytes()
        ).hexdigest(),
        "selectedEdgeCount": len(edges),
        "edges": edges,
    }


def embedded_theorem_replay_certificate_source(
    graph: dict[str, Any], reconstructed_proof: Path
) -> str:
    proof = reconstructed_proof.read_text(encoding="utf-8")
    body = without_import_commands(proof)
    scope_count = unclosed_command_scope_count(body)
    spec = concrete_semantic_replay_spec(graph, reconstructed_proof)
    command = concrete_semantic_replay_command(spec)
    lines = [
        "import GraphCertificate",
        "import Mathlib",
        "",
        "/- Generated concrete semantic dependency certificate.",
        "The reconstructed accepted proof below supplies the proof pieces;",
        "the final command kernel-checks and compares every selected edge. -/",
        f"-- graph_id: {safe_lean_comment(str(graph['graph_id']))}",
        "-- certificate_kind: embedded_theorem_replay",
        f"-- topology_sha256: {topology_fingerprint(graph)}",
        f"-- reconstructed_proof_sha256: {spec['reconstructedProofSha256']}",
        f"-- selected_edge_count: {spec['selectedEdgeCount']}",
        "",
        body,
        "",
        *(["end"] * scope_count),
        "",
        command,
        "",
    ]
    return "\n".join(lines)


def concrete_semantic_replay_command(spec: dict[str, Any]) -> str:
    payload = json.dumps(
        spec, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )
    lean_theorem_string = json.dumps(str(spec["theoremName"]), ensure_ascii=False)
    lean_payload_string = json.dumps(payload, ensure_ascii=False)
    return f"#check_dependency_graph {lean_theorem_string} against {lean_payload_string}"


def concrete_semantic_certificate_source(
    graph: dict[str, Any], reconstructed_proof: Path | None = None
) -> str:
    if concrete_semantic_certificate_kind(graph) == "reviewed_edge_theorems":
        return reviewed_concrete_semantic_certificate_source(graph)
    if reconstructed_proof is None or not reconstructed_proof.is_file():
        raise FileNotFoundError(
            f"reconstructed proof is required for {graph['graph_id']} semantic replay"
        )
    return embedded_theorem_replay_certificate_source(graph, reconstructed_proof)


def concrete_semantic_certificate_errors(
    graph: dict[str, Any], source: str, reconstructed_proof: Path | None = None
) -> list[str]:
    """Check that a concrete Lean certificate is tied to this exact graph."""

    errors: list[str] = []
    kind = concrete_semantic_certificate_kind(graph)
    expected_metadata = {
        "graph_id": str(graph["graph_id"]),
        "certificate_kind": kind,
        "topology_sha256": topology_fingerprint(graph),
        "selected_edge_count": str(sum(
            bool(edge.get("selected")) for edge in graph["hyperedges"]
        )),
    }
    if kind == "reviewed_edge_theorems":
        expected_metadata["generated_bridge_topology_sha256"] = topology_fingerprint(graph)
    for key, expected in expected_metadata.items():
        values = certificate_metadata_values(source, key)
        if values != [expected]:
            errors.append(
                f"concrete certificate {key} metadata is {values!r}; expected {expected!r}"
            )

    theorem_name = str((graph.get("task") or {}).get("theorem_name") or "")
    if kind == "reviewed_edge_theorems":
        expected_edge_ids = {
            str(edge["id"]) for edge in graph["hyperedges"] if edge.get("selected")
        }
        declared_edge_ids = set(re.findall(
            r"^theorem\s+edge_([A-Za-z0-9_]+)\b", source, flags=re.MULTILINE
        ))
        if declared_edge_ids != expected_edge_ids:
            errors.append(
                "concrete certificate edge theorem ids differ from selected graph edges: "
                f"missing={sorted(expected_edge_ids - declared_edge_ids)}, "
                f"extra={sorted(declared_edge_ids - expected_edge_ids)}"
            )
        anchor = "graph_derives_" + theorem_name
        if not re.search(rf"^theorem\s+{re.escape(anchor)}\b", source, flags=re.MULTILINE):
            errors.append(f"concrete certificate lacks final anchor theorem {anchor}")
    else:
        command_pattern = (
            rf"^#check_dependency_graph\s+{re.escape(json.dumps(theorem_name))}\s+against\s+"
        )
        if len(re.findall(command_pattern, source, flags=re.MULTILINE)) != 1:
            errors.append("embedded theorem replay lacks its unique Lean checking command")

    unsafe = forbidden_tokens(source, ("sorry", "admit", "axiom"))
    if unsafe:
        errors.append(
            "concrete certificate contains unsafe declarations/tokens: "
            + ", ".join(unsafe)
        )

    proof_hashes = certificate_metadata_values(source, "reconstructed_proof_sha256")
    if reconstructed_proof is not None and reconstructed_proof.is_file():
        expected_proof_hash = hashlib.sha256(reconstructed_proof.read_bytes()).hexdigest()
        if proof_hashes != [expected_proof_hash]:
            errors.append(
                "concrete certificate reconstructed-proof hash does not match proof.lean"
            )
    elif len(proof_hashes) != 1 or not re.fullmatch(r"[0-9a-f]{64}", proof_hashes[0]):
        errors.append("concrete certificate has invalid reconstructed-proof metadata")
    return errors


def install_concrete_semantic_certificates(
    graphs: Sequence[dict[str, Any]], graph_root: Path
) -> None:
    """Install graph-specific, self-contained semantic edge certificates."""

    for graph in graphs:
        template_path = CONCRETE_SEMANTIC_CERTIFICATE_TEMPLATES.get(graph["graph_id"])
        if template_path is not None and not template_path.is_file():
            raise FileNotFoundError(
                f"missing concrete semantic certificate template: {template_path}"
            )
        graph_dir = graph_root / graph["graph_id"]
        proof_path = (
            graph_dir / str(graph["sources"]["reconstructed_proof"])
        ).resolve()
        source = concrete_semantic_certificate_source(graph, proof_path)
        consistency_errors = concrete_semantic_certificate_errors(
            graph, source, proof_path
        )
        if consistency_errors:
            raise ValueError("; ".join(consistency_errors))

        destination = graph_dir / CONCRETE_SEMANTIC_CERTIFICATE_FILENAME
        destination.write_text(source, encoding="utf-8")
        source_hash = hashlib.sha256(source.encode("utf-8")).hexdigest()
        graph["sources"].update({
            "concrete_semantic_certificate": CONCRETE_SEMANTIC_CERTIFICATE_FILENAME,
            "concrete_semantic_certificate_kind": concrete_semantic_certificate_kind(graph),
            "concrete_semantic_certificate_sha256": source_hash,
            "concrete_semantic_topology_sha256": topology_fingerprint(graph),
        })
        graph["validation"]["lean_concrete_semantic_certificate"] = "pending"
        graph["validation"]["standalone_source_level_semantic_edge_replay"] = "pending"


def concrete_semantic_batch_member_source(
    graph: dict[str, Any], reconstructed_proof: Path
) -> str:
    graph_id = str(graph["graph_id"])
    namespace = "Rollout_" + graph_id
    if concrete_semantic_certificate_kind(graph) == "reviewed_edge_theorems":
        body = without_import_commands(
            concrete_semantic_certificate_source(graph, reconstructed_proof)
        )
        scope_count = unclosed_command_scope_count(body)
        return "\n".join([
            f"namespace {namespace}",
            "",
            body,
            "",
            *(["end"] * scope_count),
            f"end {namespace}",
            "",
        ])

    proof = reconstructed_proof.read_text(encoding="utf-8")
    body = without_import_commands(proof)
    scope_count = unclosed_command_scope_count(body)
    spec = concrete_semantic_replay_spec(graph, reconstructed_proof)
    spec["theoremName"] = namespace + "." + str(graph["task"]["theorem_name"])
    return "\n".join([
        f"namespace {namespace}",
        "",
        f"-- graph_id: {safe_lean_comment(graph_id)}",
        f"-- topology_sha256: {topology_fingerprint(graph)}",
        body,
        "",
        *(["end"] * scope_count),
        f"end {namespace}",
        "",
        concrete_semantic_replay_command(spec),
        "",
    ])


def concrete_semantic_batch_source(
    graphs: Sequence[dict[str, Any]], output_root: Path
) -> str:
    members = ["import GraphCertificate", "import Mathlib", ""]
    for graph in graphs:
        graph_dir = output_root / "graphs" / graph["graph_id"]
        proof_path = (
            graph_dir / str(graph["sources"]["reconstructed_proof"])
        ).resolve()
        members.append(concrete_semantic_batch_member_source(graph, proof_path))
    return "\n".join(members)


def run_concrete_semantic_lean_checks(
    graphs: Sequence[dict[str, Any]], output_root: Path, quiet: bool = False,
    batch_size: int = 20,
) -> dict[str, Any]:
    """Fresh-compile concrete certificates in isolated, bisectable batches."""

    selected = sorted(
        [
            graph for graph in graphs
            if (graph.get("sources") or {}).get("concrete_semantic_certificate")
        ],
        key=lambda item: item["graph_id"],
    )
    if batch_size < 1:
        raise ValueError("concrete semantic certificate batch size must be positive")
    if any(
        concrete_semantic_certificate_kind(graph) == "embedded_theorem_replay"
        for graph in selected
    ):
        built = subprocess.run(
            ["lake", "build", "graph_certificate"],
            cwd=EXPERIMENT_ROOT,
            text=True,
            capture_output=True,
        )
        if built.returncode != 0:
            raise RuntimeError(
                "could not build GraphCertificate checker: "
                + (built.stderr or built.stdout)[-2000:]
            )

    batch_root = output_root / "certificates" / "semantic_batches"
    batch_root.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, Any]] = []
    attempts: list[dict[str, Any]] = []

    def original_isolation_mode(graph: dict[str, Any]) -> str:
        graph_dir = output_root / "graphs" / graph["graph_id"]
        raw_path = (
            graph_dir / str(graph["sources"]["raw_elaboration"])
        ).resolve()
        raw = json.loads(raw_path.read_text(encoding="utf-8"))
        return str((raw.get("batch_provenance") or {}).get("isolation_mode") or "")

    def certificate_record(
        graph: dict[str, Any], completed: subprocess.CompletedProcess[str],
        mode: str, batch_path: Path,
    ) -> dict[str, Any]:
        relative = str(graph["sources"]["concrete_semantic_certificate"])
        path = output_root / "graphs" / graph["graph_id"] / relative
        return {
            "graph_id": graph["graph_id"],
            "certificate_kind": concrete_semantic_certificate_kind(graph),
            "status": "passed" if completed.returncode == 0 else "failed",
            "validation_mode": mode,
            "source": str(path),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "topology_sha256": topology_fingerprint(graph),
            "lean_source": str(batch_path),
            "returncode": completed.returncode,
            "stdout": completed.stdout if mode != "successful_batch" else "",
            "stderr": completed.stderr if mode != "successful_batch" else "",
        }

    def compile_group(group: Sequence[dict[str, Any]]) -> None:
        source = concrete_semantic_batch_source(group, output_root)
        digest = hashlib.sha256(source.encode("utf-8")).hexdigest()[:16]
        batch_path = batch_root / f"batch_{digest}.lean"
        batch_path.write_text(source, encoding="utf-8")
        if not quiet:
            print(
                f"[semantic batch] checking {len(group)} graph(s): {digest}",
                flush=True,
            )
        completed = subprocess.run(
            ["lake", "env", "lean", str(batch_path)],
            cwd=EXPERIMENT_ROOT,
            text=True,
            capture_output=True,
        )
        attempts.append({
            "source": str(batch_path),
            "source_sha256": hashlib.sha256(batch_path.read_bytes()).hexdigest(),
            "graph_ids": [graph["graph_id"] for graph in group],
            "returncode": completed.returncode,
            "stdout": completed.stdout,
            "stderr": completed.stderr,
        })
        if completed.returncode == 0:
            if not quiet:
                print(
                    f"[semantic batch] passed {len(group)} graph(s): {digest}",
                    flush=True,
                )
            records.extend(
                certificate_record(graph, completed, "successful_batch", batch_path)
                for graph in group
            )
            return
        if not quiet:
            diagnostic = (completed.stderr or completed.stdout).strip()
            if diagnostic:
                print(
                    "[semantic batch diagnostic]\n" + diagnostic[-2400:],
                    flush=True,
                )
        if len(group) > 1:
            if not quiet:
                print(
                    f"[semantic batch] bisecting failed group: {digest}",
                    flush=True,
                )
            midpoint = len(group) // 2
            compile_group(group[:midpoint])
            compile_group(group[midpoint:])
            return

        graph = group[0]
        certificate_path = (
            output_root / "graphs" / graph["graph_id"]
            / str(graph["sources"]["concrete_semantic_certificate"])
        )
        fallback = subprocess.run(
            ["lake", "env", "lean", str(certificate_path)],
            cwd=EXPERIMENT_ROOT,
            text=True,
            capture_output=True,
        )
        if not quiet:
            print(
                f"[semantic fallback] {graph['graph_id']}: "
                + ("passed" if fallback.returncode == 0 else "failed"),
                flush=True,
            )
        records.append(certificate_record(
            graph, fallback, "individual_fallback", certificate_path
        ))

    standalone = [
        graph for graph in selected
        if original_isolation_mode(graph) == "standalone_source"
    ]
    batchable = [graph for graph in selected if graph not in standalone]
    for graph in standalone:
        path = (
            output_root / "graphs" / graph["graph_id"]
            / str(graph["sources"]["concrete_semantic_certificate"])
        )
        if not quiet:
            print(f"[semantic standalone] checking {graph['graph_id']}", flush=True)
        completed = subprocess.run(
            ["lake", "env", "lean", str(path)],
            cwd=EXPERIMENT_ROOT,
            text=True,
            capture_output=True,
        )
        attempts.append({
            "source": str(path),
            "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "graph_ids": [graph["graph_id"]],
            "returncode": completed.returncode,
            "stdout": completed.stdout,
            "stderr": completed.stderr,
        })
        records.append(certificate_record(
            graph, completed, "original_standalone_source", path
        ))
        if not quiet:
            print(
                f"[semantic standalone] {graph['graph_id']}: "
                + ("passed" if completed.returncode == 0 else "failed"),
                flush=True,
            )

    for start in range(0, len(batchable), batch_size):
        compile_group(batchable[start : start + batch_size])

    records.sort(key=lambda item: item["graph_id"])
    by_id = {record["graph_id"]: record for record in records}
    for graph in selected:
        passed = by_id[graph["graph_id"]]["status"] == "passed"
        status = "passed_in_fresh_lean_process" if passed else "failed"
        graph["validation"]["lean_concrete_semantic_certificate"] = status
        graph["validation"]["standalone_source_level_semantic_edge_replay"] = status

    failed = [record for record in records if record["status"] != "passed"]
    report = {
        "schema_version": "lean_concrete_semantic_certificate_report_v2",
        "status": "passed" if not failed else "failed",
        "certificate_count": len(records),
        "batch_attempt_count": len(attempts),
        "batch_attempts": attempts,
        "certificates": records,
    }
    write_json(output_root / "concrete_semantic_validation.json", report)
    if failed:
        diagnostic = failed[0]["stderr"] or failed[0]["stdout"]
        raise RuntimeError(
            "Lean concrete semantic certificate failed for "
            + failed[0]["graph_id"] + ": " + diagnostic[-2000:]
        )
    if not quiet:
        print(
            f"Lean checked {len(records)} concrete semantic certificates "
            f"in {len(attempts)} batch attempt(s)"
        )
    return report


def wrap_label(value: str, width: int = 30, lines: int = 4) -> list[str]:
    chunks = textwrap.wrap(value, width=width, break_long_words=True, break_on_hyphens=False)
    if len(chunks) > lines:
        chunks = chunks[:lines]
        chunks[-1] = chunks[-1][:-1] + "…" if chunks[-1] else "…"
    return chunks or [""]


def render_svg(graph: dict[str, Any], path: Path) -> None:
    selected_nodes = [item for item in graph["nodes"] if item.get("selected")]
    selected_edges = [item for item in graph["hyperedges"] if item.get("selected")]
    depths = graph_layers(graph)
    by_depth: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for node in selected_nodes:
        by_depth[depths[node["id"]]].append(node)
    for values in by_depth.values():
        values.sort(key=lambda item: item["id"])
    max_depth = max(by_depth, default=0)
    max_rows = max((len(values) for values in by_depth.values()), default=1)
    x_gap, y_gap = 470, 160
    width = max(760, 180 + (max_depth + 1) * x_gap)
    height = max(360, 160 + max_rows * y_gap)
    node_w, node_h = 260, 88
    positions: dict[str, tuple[float, float]] = {}
    for layer, values in by_depth.items():
        total = (len(values) - 1) * y_gap
        start_y = height / 2 - total / 2
        for row, node in enumerate(values):
            positions[node["id"]] = (80 + layer * x_gap, start_y + row * y_gap)

    colors = {
        "manifest": ("#E7F6F3", "#178F82"),
        "local_assumption": ("#F2F3F5", "#68717A"),
        "derived": ("#FFF4E5", "#D97706"),
        "goal": ("#EAF7EC", "#2E8B57"),
    }
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#315A7D"/></marker></defs>',
        '<rect width="100%" height="100%" fill="white"/>',
        f'<text x="28" y="32" font-family="Helvetica,Arial,sans-serif" font-size="18" font-weight="700" fill="#17324D">{html.escape(graph["task"]["theorem_name"])}</text>',
    ]
    for edge in selected_edges:
        cx, cy = positions[edge["conclusion"]]
        premise_positions = [positions[p] for p in edge["premises"] if p in positions]
        if premise_positions:
            px = max(x + node_w for x, _ in premise_positions)
            rule_x = (px + cx) / 2
        else:
            rule_x = cx - 120
        rule_y = sum((y for _, y in premise_positions), cy) / (len(premise_positions) + 1)
        for premise in edge["premises"]:
            if premise not in positions:
                continue
            x, y = positions[premise]
            parts.append(f'<path d="M {x + node_w} {y} L {rule_x - 15} {rule_y}" stroke="#315A7D" stroke-width="1.8" fill="none" marker-end="url(#arrow)"/>')
        parts.append(f'<path d="M {rule_x + 15} {rule_y} L {cx} {cy}" stroke="#315A7D" stroke-width="1.8" fill="none" marker-end="url(#arrow)"/>')
        parts.append(f'<polygon points="{rule_x},{rule_y - 17} {rule_x + 17},{rule_y} {rule_x},{rule_y + 17} {rule_x - 17},{rule_y}" fill="#FFF0DB" stroke="#D97706" stroke-width="1.8"/>')
        for offset, line in enumerate(wrap_label(edge["rule"]["label"], width=27, lines=3)):
            label = html.escape(line)
            parts.append(f'<text x="{rule_x}" y="{rule_y + 32 + offset*12}" text-anchor="middle" font-family="Helvetica,Arial,sans-serif" font-size="9" fill="#7C4300">{label}</text>')
        if edge["retrieval"]["observed_search_event_ids"]:
            ry = max(55, rule_y - 53)
            parts.append(f'<rect x="{rule_x - 61}" y="{ry - 15}" width="122" height="27" rx="7" fill="#F3ECFF" stroke="#7D4CC2" stroke-width="1.2"/>')
            rlabel = html.escape(", ".join(edge["retrieval"]["observed_search_event_ids"][:2]))
            parts.append(f'<text x="{rule_x}" y="{ry + 3}" text-anchor="middle" font-family="Helvetica,Arial,sans-serif" font-size="10" fill="#60349A">retrieved {rlabel}</text>')
            parts.append(f'<path d="M {rule_x} {ry + 12} L {rule_x} {rule_y - 18}" stroke="#7D4CC2" stroke-width="1.2" stroke-dasharray="5 4" fill="none"/>')

    for node in selected_nodes:
        x, y = positions[node["id"]]
        fill, stroke = colors.get(node["origin"], colors["derived"])
        if node["class"] == "side":
            fill, stroke = "#F4F4F4", "#80868B"
        parts.append(f'<rect x="{x}" y="{y - node_h/2}" width="{node_w}" height="{node_h}" rx="11" fill="{fill}" stroke="{stroke}" stroke-width="2"/>')
        parts.append(f'<text x="{x + 10}" y="{y - 20}" font-family="Helvetica,Arial,sans-serif" font-size="10" font-weight="700" fill="{stroke}">{html.escape(node["binding_name"])}</text>')
        for offset, line in enumerate(wrap_label(node["statement"])):
            parts.append(f'<text x="{x + node_w/2}" y="{y - 2 + offset*14}" text-anchor="middle" font-family="Menlo,monospace" font-size="10" fill="#23384D">{html.escape(line)}</text>')
    parts.append('</svg>')
    path.write_text("\n".join(parts) + "\n", encoding="utf-8")


def render_dot(graph: dict[str, Any], path: Path) -> None:
    lines = ["digraph dependency_graph {", "  rankdir=LR;", "  graph [bgcolor=white];", "  node [fontname=Helvetica];"]
    for node in graph["nodes"]:
        if not node.get("selected"):
            continue
        shape = "doubleoctagon" if node["origin"] == "goal" else "box"
        color = "#178F82" if node["origin"] == "manifest" else "#D97706"
        label = (node["binding_name"] + "\\n" + node["statement"]).replace('"', '\\"')
        lines.append(f'  "{node["id"]}" [shape={shape}, color="{color}", label="{label}"];')
    for edge in graph["hyperedges"]:
        if not edge.get("selected"):
            continue
        rule_id = "r_" + edge["id"]
        label = edge["rule"]["label"].replace('"', '\\"')
        lines.append(f'  "{rule_id}" [shape=diamond, label="{label}", color="#D97706"];')
        for premise in edge["premises"]:
            lines.append(f'  "{premise}" -> "{rule_id}";')
        lines.append(f'  "{rule_id}" -> "{edge["conclusion"]}";')
    lines.append("}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def render_markdown(graph: dict[str, Any], path: Path) -> None:
    metrics = graph["metrics"]
    lines = [
        f"# {graph['task']['theorem_name']}", "",
        f"- Problem index: `{graph['task']['problem_idx']}`",
        f"- arXiv source: `{graph['task']['source']}`",
        f"- Selected nodes / hyperedges: **{metrics['selected_node_count']} / {metrics['selected_hyperedge_count']}**",
        f"- Selected depth: **{metrics['selected_depth']}**",
        f"- Retrieval events matched: **{metrics['useful_retrieval_event_count']} / {metrics['retrieval_query_count']}**",
        f"- Incomplete target InfoTree snapshots audited/excluded: **{metrics['excluded_info_tree_binding_count']}**",
        "- Validation: original proof re-elaborated; every edge witness kernel-checked in its Lean local context; selected topology compiled as a separate Lean theorem.",
        f"- Axioms: `{', '.join(graph['axiom_audit']['axioms']) or 'none'}`",
    ]
    if (graph.get("sources") or {}).get("concrete_semantic_certificate"):
        if graph["sources"].get("concrete_semantic_certificate_kind") == "reviewed_edge_theorems":
            description = (
                "contains a checked theorem for every selected edge and composes "
                "them into the final theorem"
            )
        else:
            description = (
                "embeds the accepted proof and checks every selected raw witness, "
                "premise list, and conclusion against this graph"
            )
        lines.append(
            "- Concrete certificate: [semantic_graph_certificate.lean]"
            f"(semantic_graph_certificate.lean) {description}."
        )
    lines.extend([
        "", "![dependency graph](graph.svg)", "", "## Hyperedges", "",
        "| Edge | Premises | Conclusion | Rule | Retrieval |", "|---|---|---|---|---|",
    ])
    nodes = {item["id"]: item for item in graph["nodes"]}
    for edge in graph["hyperedges"]:
        if not edge.get("selected"):
            continue
        premises = ", ".join(nodes[item]["binding_name"] for item in edge["premises"]) or "∅"
        conclusion = nodes[edge["conclusion"]]["binding_name"]
        retrieval = ", ".join(edge["retrieval"]["observed_search_event_ids"]) or "—"
        lines.append(f"| `{edge['id']}` | {premises} | {conclusion} | `{edge['rule']['label']}` | {retrieval} |")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_index(graphs: Sequence[dict[str, Any]], output_root: Path) -> None:
    lines = [
        "# Lean rollout dependency-graph pilot", "",
        f"{len(graphs)} sound, structured rollouts selected under the cohort config. Each graph is extracted from Lean-elaborated proposition bindings; retrieval is an overlay, not a reasoning node.",
        "",
        "See [cohort_report.md](cohort_report.md) for sampling, validation layers, distributions, and a compact gallery.",
        "", "| Graph | Source | Nodes | Edges | Depth | Snapshots excluded | Retrieval matched |", "|---|---|---:|---:|---:|---:|---:|",
    ]
    for graph in graphs:
        metrics = graph["metrics"]
        slug = graph["graph_id"]
        lines.append(
            f"| [{graph['task']['theorem_name']}](graphs/{slug}/graph.md) | `{graph['task']['source']}` | "
            f"{metrics['selected_node_count']} | {metrics['selected_hyperedge_count']} | {metrics['selected_depth']} | "
            f"{metrics['excluded_info_tree_binding_count']} | "
            f"{metrics['useful_retrieval_event_count']}/{metrics['retrieval_query_count']} |"
        )
    lines.extend([
        "", "## Validation boundary", "",
        "The final submissions and accepted helpers are re-elaborated under Lean/Mathlib 4.29.0. Lean's kernel checks each emitted local witness in its original local context; transient InfoTree bindings with unresolved metavariables are counted and excluded. Dependency fingerprints tie every rendered edge back to checked evidence, and `topology_certificate.lean` proves the selected closure composes to the goal. Every graph also has a self-contained `semantic_graph_certificate.lean`: it embeds the accepted proof and rechecks the selected raw witnesses, exact proposition premises, and conclusions. The reviewed p1662 variant additionally exposes one theorem per selected edge and composes them into the final theorem. This establishes a sound selected-proof projection, not a complete editor trace or a unique/globally minimal mathematical decomposition.",
    ])
    (output_root / "index.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_cohort_report(
    graphs: Sequence[dict[str, Any]], output_root: Path, config: dict[str, Any],
    distributions: dict[str, dict[str, int]],
) -> None:
    def median(values: Sequence[int]) -> float:
        ordered = sorted(values)
        middle = len(ordered) // 2
        if len(ordered) % 2:
            return float(ordered[middle])
        return (ordered[middle - 1] + ordered[middle]) / 2

    depths = [int(graph["metrics"]["selected_depth"]) for graph in graphs]
    edges = [int(graph["metrics"]["selected_hyperedge_count"]) for graph in graphs]
    fanins = [int(graph["metrics"]["max_fan_in_all"]) for graph in graphs]
    exclusions = [
        int(graph["metrics"]["excluded_info_tree_binding_count"])
        for graph in graphs
    ]
    concrete_count = sum(
        bool((graph.get("sources") or {}).get("concrete_semantic_certificate"))
        for graph in graphs
    )
    gallery_candidates = [
        max(graphs, key=lambda graph: (graph["metrics"]["selected_depth"], graph["graph_id"])),
        max(graphs, key=lambda graph: (graph["metrics"]["selected_hyperedge_count"], graph["graph_id"])),
        max(graphs, key=lambda graph: (graph["metrics"]["max_fan_in_all"], graph["graph_id"])),
        max(graphs, key=lambda graph: (graph["metrics"]["retrieval_query_count"], graph["graph_id"])),
        max(graphs, key=lambda graph: (graph["metrics"]["useful_retrieval_event_count"], graph["graph_id"])),
    ] if graphs else []
    ordered = sorted(
        graphs,
        key=lambda graph: (
            graph["metrics"]["selected_depth"],
            graph["metrics"]["selected_hyperedge_count"],
            graph["graph_id"],
        ),
    )
    if ordered:
        for numerator in range(0, 6):
            gallery_candidates.append(ordered[round((len(ordered) - 1) * numerator / 5)])
    gallery: list[dict[str, Any]] = []
    seen: set[str] = set()
    for graph in gallery_candidates:
        if graph["graph_id"] not in seen:
            gallery.append(graph)
            seen.add(graph["graph_id"])

    policy = config["selection"]
    lines = [
        "# Structured Lean dependency-graph cohort", "",
        f"This cohort contains **{len(graphs)}** successful rollouts. Selection strategy: "
        f"`{policy.get('strategy')}`; seed: `{policy.get('seed', 'none')}`.", "",
        "## What is checked", "",
        "1. **Rollout gate:** the recorded `verify_submission` passed and placeholder tokens/warnings are absent.",
        "2. **Semantic proof evidence:** the reconstructed theorem and accepted helper declarations elaborate under pinned Lean/Mathlib 4.29.0.",
        "3. **Edge witnesses:** Lean's kernel type-checks every emitted proof value in its exact original local context, and its type is definitionally equal to the rendered conclusion. Transient target InfoTree bindings containing metavariables are audited and excluded, never promoted to edges.",
        "4. **Projection link:** a SHA-256 dependency record ties the rendered premises and conclusion to the raw Lean evidence.",
        "5. **Graph composition:** a generated `topology_certificate.lean` theorem composes precisely the selected hyperedges from boundary facts to the goal in a fresh Lean process.",
        f"6. **Concrete replay:** all {concrete_count} graph(s) include a self-contained `semantic_graph_certificate.lean`. Lean replays the accepted theorem value, kernel-checks each selected raw witness, and compares its ordered proposition premises and conclusion with the embedded graph manifest. The reviewed p1662 certificate additionally names one theorem per selected graph edge and composes only those theorems into the final result.",
        "7. **Axiom audit:** transitive axioms are recorded; `sorryAx`-like dependencies fail validation.", "",
        "The result is sound for the selected proof and projection policy. It is not a claim of uniqueness, task-level premise necessity, or globally minimum depth.", "",
        "## Cohort summary", "",
        "| Measure | Min | Median | Max |", "|---|---:|---:|---:|",
        f"| Selected depth | {min(depths, default=0)} | {median(depths) if depths else 0:g} | {max(depths, default=0)} |",
        f"| Selected hyperedges | {min(edges, default=0)} | {median(edges) if edges else 0:g} | {max(edges, default=0)} |",
        f"| Maximum fan-in | {min(fanins, default=0)} | {median(fanins) if fanins else 0:g} | {max(fanins, default=0)} |",
        f"| Excluded incomplete InfoTree snapshots | {min(exclusions, default=0)} | {median(exclusions) if exclusions else 0:g} | {max(exclusions, default=0)} |",
        "", "## Distributions", "",
    ]
    for name, counts in distributions.items():
        lines.extend([
            f"### {name.replace('_', ' ').title()}", "",
            "| Value | Graphs |", "|---:|---:|",
            *(f"| `{value}` | {count} |" for value, count in counts.items()),
            "",
        ])
    lines.extend(["## Gallery", "", "| Graph | Depth | Edges | Fan-in |", "|---|---:|---:|---:|"])
    for graph in gallery:
        metrics = graph["metrics"]
        lines.append(
            f"| [{graph['task']['theorem_name']}](graphs/{graph['graph_id']}/graph.md) | "
            f"{metrics['selected_depth']} | {metrics['selected_hyperedge_count']} | "
            f"{metrics['max_fan_in_all']} |"
        )
    lines.extend([
        "", "## Recommended analysis unit", "",
        "Use one row per graph for corpus-level summaries, one row per selected hyperedge for rule/retrieval analysis, and keep rejected attempts in a separate rollout table. Do not mix temporal proof-state transitions with forward semantic hyperedges.",
    ])
    (output_root / "cohort_report.md").write_text(
        "\n".join(lines) + "\n", encoding="utf-8"
    )


def validate_graph_artifact(
    graph_path: Path, forbidden: Sequence[str]
) -> dict[str, Any]:
    errors: list[str] = []
    try:
        graph = json.loads(graph_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return {"graph": str(graph_path), "status": "failed", "errors": [str(exc)]}

    if graph.get("schema_version") != "manifest_dependency_hypergraph_v2":
        errors.append("unexpected graph schema version")
    nodes_list = graph.get("nodes") or []
    edges = graph.get("hyperedges") or []
    node_ids = [str(node.get("id")) for node in nodes_list]
    edge_ids = [str(edge.get("id")) for edge in edges]
    if len(node_ids) != len(set(node_ids)):
        errors.append("duplicate node ids")
    if len(edge_ids) != len(set(edge_ids)):
        errors.append("duplicate hyperedge ids")
    nodes = {str(node.get("id")): node for node in nodes_list}
    goal = str((graph.get("task") or {}).get("goal_node") or "")
    if goal not in nodes:
        errors.append("goal node is missing")
    for edge in edges:
        if edge.get("conclusion") not in nodes:
            errors.append(f"{edge.get('id')}: unknown conclusion")
        unknown = sorted(set(edge.get("premises") or []) - set(nodes))
        if unknown:
            errors.append(f"{edge.get('id')}: unknown premises {unknown}")

    selected_edges = [edge for edge in edges if edge.get("selected")]
    selected_nodes = {node["id"] for node in nodes_list if node.get("selected")}
    incoming: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in selected_edges:
        incoming[str(edge.get("conclusion"))].append(edge)
    multiply_derived = sorted(node_id for node_id, rows in incoming.items() if len(rows) > 1)
    if multiply_derived:
        errors.append(f"multiple selected producers for {multiply_derived}")

    closure_nodes: set[str] = set()
    closure_edges: set[str] = set()
    agenda = [goal] if goal in nodes else []
    while agenda:
        node_id = agenda.pop()
        if node_id in closure_nodes:
            continue
        closure_nodes.add(node_id)
        producers = incoming.get(node_id, [])
        if len(producers) == 1:
            edge = producers[0]
            closure_edges.add(str(edge.get("id")))
            agenda.extend(str(item) for item in edge.get("premises") or [])
    if selected_nodes != closure_nodes:
        errors.append("selected nodes are not exactly the backward goal closure")
    if {str(edge.get("id")) for edge in selected_edges} != closure_edges:
        errors.append("selected hyperedges are not exactly the backward goal closure")

    if not errors and goal:
        integrity = validate_and_measure(nodes, edges, goal)
        validation = graph.get("validation") or {}
        if not integrity["acyclic"]:
            errors.append("selected graph contains a cycle")
        if not integrity["goal_reachable"]:
            errors.append("selected goal dependency closure is unresolved")
        if integrity["unresolved"]:
            errors.append(f"unresolved selected nodes: {integrity['unresolved']}")
        for key, value in integrity["metrics"].items():
            if (graph.get("metrics") or {}).get(key) != value:
                errors.append(f"stored metric differs from recomputation: {key}")
        if validation.get("acyclic") != integrity["acyclic"]:
            errors.append("stored acyclic flag differs from recomputation")
        if validation.get("goal_reachable") != integrity["goal_reachable"]:
            errors.append("stored goal_reachable flag differs from recomputation")

    for filename in ("graph.svg", "graph.dot", "graph.md", "topology_certificate.lean"):
        if not (graph_path.parent / filename).is_file():
            errors.append(f"missing sidecar {filename}")
    certificate_path = graph_path.parent / "topology_certificate.lean"
    if certificate_path.is_file():
        expected_certificate = topology_certificate_source(graph, include_import=True)
        if certificate_path.read_text(encoding="utf-8") != expected_certificate:
            errors.append("topology certificate is not the deterministic projection of graph.json")
        expected_topology_hash = topology_fingerprint(graph)
        if (graph.get("sources") or {}).get("topology_sha256") != expected_topology_hash:
            errors.append("stored topology fingerprint differs from graph topology")
    svg_path = graph_path.parent / "graph.svg"
    if svg_path.is_file():
        try:
            root = ET.parse(svg_path).getroot()
            if not root.tag.endswith("svg"):
                errors.append("SVG root element is invalid")
        except ET.ParseError as exc:
            errors.append(f"invalid SVG XML: {exc}")
    dot_path = graph_path.parent / "graph.dot"
    if dot_path.is_file():
        dot = dot_path.read_text(encoding="utf-8").strip()
        if not dot.startswith("digraph ") or not dot.endswith("}"):
            errors.append("DOT wrapper is invalid")

    sources = graph.get("sources") or {}
    proof_path = (graph_path.parent / str(sources.get("reconstructed_proof") or "")).resolve()
    raw_path = (graph_path.parent / str(sources.get("raw_elaboration") or "")).resolve()
    concrete_path = graph_path.parent / CONCRETE_SEMANTIC_CERTIFICATE_FILENAME
    validation = graph.get("validation") or {}
    expected_kind = concrete_semantic_certificate_kind(graph)
    if sources.get("concrete_semantic_certificate") != CONCRETE_SEMANTIC_CERTIFICATE_FILENAME:
        errors.append("concrete semantic certificate source is not recorded")
    if sources.get("concrete_semantic_certificate_kind") != expected_kind:
        errors.append("stored concrete semantic certificate kind differs")
    if not concrete_path.is_file():
        errors.append(f"missing sidecar {CONCRETE_SEMANTIC_CERTIFICATE_FILENAME}")
    elif proof_path.is_file():
        concrete_source = concrete_path.read_text(encoding="utf-8")
        expected_source = concrete_semantic_certificate_source(graph, proof_path)
        if concrete_source != expected_source:
            errors.append(
                "concrete semantic certificate is not its deterministic "
                "proof-and-graph projection"
            )
        errors.extend(concrete_semantic_certificate_errors(
            graph, concrete_source, proof_path
        ))
        concrete_hash = hashlib.sha256(concrete_path.read_bytes()).hexdigest()
        if sources.get("concrete_semantic_certificate_sha256") != concrete_hash:
            errors.append("stored concrete semantic certificate hash differs")
        if sources.get("concrete_semantic_topology_sha256") != topology_fingerprint(graph):
            errors.append("stored concrete semantic topology hash differs")
    expected_status = "passed_in_fresh_lean_process"
    if validation.get("lean_concrete_semantic_certificate") != expected_status:
        errors.append("concrete semantic Lean validation did not pass")
    if validation.get("standalone_source_level_semantic_edge_replay") != expected_status:
        errors.append("standalone semantic edge replay did not pass")
    if not proof_path.is_file():
        errors.append("reconstructed proof source is missing")
    else:
        unsafe = forbidden_tokens(proof_path.read_text(encoding="utf-8"), forbidden)
        if unsafe:
            errors.append("reconstructed proof contains forbidden tokens: " + ", ".join(unsafe))
    if not raw_path.is_file():
        errors.append("raw elaboration evidence is missing")
    else:
        raw = json.loads(raw_path.read_text(encoding="utf-8"))
        if raw.get("schema_version") != "lean_proof_term_projection_raw_v4":
            errors.append("unexpected raw elaboration schema version")
        if raw.get("lean_version") != "4.29.0":
            errors.append("raw elaboration Lean version is not 4.29.0")
        export_name = str(sources.get("batch_export_theorem_name") or "")
        provenance = raw.get("batch_provenance") or {}
        isolation_mode = provenance.get("isolation_mode")
        if isolation_mode not in {"generated_namespace_batch", "standalone_source"}:
            errors.append("raw evidence has an invalid isolation mode")
        if provenance.get("export_theorem_name") != export_name:
            errors.append("raw provenance theorem name differs from theorem evidence")
        if isolation_mode == "generated_namespace_batch" and not provenance.get("namespace"):
            errors.append("namespaced raw evidence lacks its namespace")
        if isolation_mode == "standalone_source" and provenance.get("namespace") is not None:
            errors.append("standalone raw evidence unexpectedly records a namespace")
        batch_source = resolve_recorded_path(str(provenance.get("source") or ""))
        if not batch_source.is_file():
            errors.append("batch provenance source is missing")
        recorded_hash = str(provenance.get("proof_sha256") or "")
        if recorded_hash and proof_path.is_file():
            proof_hash = hashlib.sha256(proof_path.read_bytes()).hexdigest()
            if recorded_hash != proof_hash:
                errors.append("raw elaboration proof hash differs from reconstructed proof")

        theorem_rows = [
            item for item in raw.get("theorems") or []
            if item.get("theorem_name") == export_name
        ]
        if len(theorem_rows) != 1:
            errors.append("raw evidence does not contain exactly one exported theorem row")
        else:
            theorem_row = theorem_rows[0]
            raw_axioms = classify_axioms(theorem_row.get("axioms") or [])
            if graph.get("axiom_audit") != raw_axioms:
                errors.append("axiom audit differs from Lean raw evidence")
            if raw_axioms["status"] != "passed":
                errors.append("Lean axiom audit contains an incomplete or unsafe axiom")
            exclusion_audit = info_tree_exclusion_audit(raw)
            projected_exclusion_audit = (
                (graph.get("projection") or {}).get("excluded_info_tree_bindings")
            )
            if projected_exclusion_audit != exclusion_audit:
                errors.append("InfoTree exclusion audit differs from Lean raw evidence")
            if (graph.get("metrics") or {}).get(
                "excluded_info_tree_binding_count"
            ) != exclusion_audit["count"]:
                errors.append("stored InfoTree exclusion count differs from Lean raw evidence")
            excluded_items = list(raw.get("excluded_local_bindings") or [])
            for item in excluded_items:
                if item.get("parent") != export_name:
                    errors.append("excluded InfoTree binding belongs to another theorem")
                if item.get("policy") != "not_emitted_as_dependency_edge":
                    errors.append("excluded InfoTree binding has an invalid exclusion policy")
                if not str(item.get("reason") or "").startswith("unresolved_metavariables_"):
                    errors.append("excluded InfoTree binding has an unexpected reason")
            raw_edges = [
                *(theorem_row.get("local_edges") or []),
                *[
                    item for item in raw.get("local_edges") or []
                    if item.get("parent") == export_name
                ],
                theorem_row.get("final_edge") or {},
            ]
            raw_by_id: dict[str, list[dict[str, Any]]] = defaultdict(list)
            for raw_edge in raw_edges:
                raw_by_id[str(raw_edge.get("id") or "")].append(raw_edge)
            emitted_info_ids = {
                str(item.get("id") or "") for item in raw.get("local_edges") or []
            }
            if any(str(item.get("id") or "") in emitted_info_ids for item in excluded_items):
                errors.append("an InfoTree binding is both emitted and excluded")
            for edge in edges:
                edge_provenance = edge.get("provenance") or {}
                raw_id = str(edge_provenance.get("raw_edge_id") or "")
                matches = raw_by_id.get(raw_id, [])
                if len(matches) != 1:
                    errors.append(f"{edge.get('id')}: raw edge id {raw_id!r} is not unique")
                    continue
                raw_edge = matches[0]
                witness = raw_edge.get("witness_check") or {}
                if not (
                    witness.get("kernel_typecheck") is True
                    and witness.get("conclusion_defeq_proof_type") is True
                    and witness.get("contains_unresolved_metavariables") is False
                ):
                    errors.append(f"{edge.get('id')}: raw Lean witness check did not pass")
                record = raw_dependency_record(raw_edge)
                projected_record = {
                    "premises": [proposition_record(nodes[item]) for item in edge.get("premises") or []],
                    "conclusion": proposition_record(nodes[str(edge.get("conclusion"))]),
                }
                if projected_record != record:
                    errors.append(f"{edge.get('id')}: projected dependency differs from Lean evidence")
                fingerprint = dependency_record_fingerprint(record)
                if edge_provenance.get("lean_dependency_record") != record:
                    errors.append(f"{edge.get('id')}: stored Lean dependency record differs")
                if edge_provenance.get("lean_dependency_sha256") != fingerprint:
                    errors.append(f"{edge.get('id')}: Lean dependency fingerprint differs")
                if edge_provenance.get("kernel_witness_check") != witness:
                    errors.append(f"{edge.get('id')}: copied kernel witness record differs")

    return {
        "graph": graph.get("graph_id", str(graph_path)),
        "status": "passed" if not errors else "failed",
        "errors": errors,
    }


def command_validate(
    config_path: Path, output_root: Path, quiet: bool = False,
    recheck_concrete: bool = True,
) -> dict[str, Any]:
    config = load_config(config_path)
    forbidden = config["selection"]["forbidden_proof_tokens"]
    graph_root = output_root / "graphs"
    graph_paths = sorted(graph_root.glob("*/graph.json"))
    global_errors: list[str] = []
    expected = int(config["sample_size"])
    if len(graph_paths) != expected:
        global_errors.append(f"found {len(graph_paths)} graphs; expected {expected}")
    results = [validate_graph_artifact(path, forbidden) for path in graph_paths]
    failures = [item for item in results if item["status"] != "passed"]

    graphs_data: list[dict[str, Any]] = []
    try:
        graphs_data = [json.loads(path.read_text(encoding="utf-8")) for path in graph_paths]
    except (OSError, json.JSONDecodeError) as exc:
        global_errors.append(f"could not load graphs for topology validation: {exc}")
    topology_batch = output_root / "certificates" / "topology_certificates.lean"
    if not topology_batch.is_file():
        global_errors.append("combined Lean topology certificate is missing")
    elif graphs_data:
        if topology_batch.read_text(encoding="utf-8") != topology_batch_source(graphs_data):
            global_errors.append("combined Lean topology certificate is stale")
        else:
            try:
                run_topology_lean_check(
                    graphs_data, topology_batch, output_root, quiet=True
                )
            except RuntimeError as exc:
                global_errors.append(str(exc))
    if graphs_data and recheck_concrete:
        try:
            run_concrete_semantic_lean_checks(
                graphs_data,
                output_root,
                quiet=True,
                batch_size=int(
                    (config.get("lean") or {}).get(
                        "semantic_certificate_batch_size", 20
                    )
                ),
            )
        except RuntimeError as exc:
            global_errors.append(str(exc))
    elif graphs_data:
        concrete_report_path = output_root / "concrete_semantic_validation.json"
        if not concrete_report_path.is_file():
            global_errors.append("concrete semantic validation report is missing")
        else:
            concrete_report = json.loads(concrete_report_path.read_text(encoding="utf-8"))
            if concrete_report.get("status") != "passed":
                global_errors.append("concrete semantic validation report did not pass")
            records = {
                str(record.get("graph_id")): record
                for record in concrete_report.get("certificates") or []
            }
            expected_ids = {str(graph["graph_id"]) for graph in graphs_data}
            if set(records) != expected_ids:
                global_errors.append(
                    "concrete semantic report graph ids differ from graph artifacts"
                )
            for graph in graphs_data:
                record = records.get(str(graph["graph_id"])) or {}
                source = (
                    output_root / "graphs" / graph["graph_id"]
                    / CONCRETE_SEMANTIC_CERTIFICATE_FILENAME
                )
                if source.is_file() and record.get("source_sha256") != hashlib.sha256(
                    source.read_bytes()
                ).hexdigest():
                    global_errors.append(
                        f"{graph['graph_id']}: concrete report source hash is stale"
                    )

    summary_path = output_root / "summary.json"
    if not summary_path.is_file():
        global_errors.append("summary.json is missing")
    else:
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        if summary.get("graph_count") != len(graph_paths):
            global_errors.append("summary graph_count does not match graph artifacts")
        summary_ids = {item.get("graph_id") for item in summary.get("graphs") or []}
        result_ids = {item.get("graph") for item in results}
        if summary_ids != result_ids:
            global_errors.append("summary graph ids do not match graph artifacts")

    report = {
        "schema_version": "dependency_graph_validation_report_v2",
        "status": "passed" if not global_errors and not failures else "failed",
        "graph_count": len(graph_paths),
        "global_errors": global_errors,
        "graphs": results,
    }
    write_json(output_root / "validation_report.json", report)
    if report["status"] != "passed":
        messages = [*global_errors, *(error for item in failures for error in item["errors"])]
        raise RuntimeError("output validation failed: " + "; ".join(messages))
    if not quiet:
        print(f"validated {len(graph_paths)} graphs: all checks passed")
    return report


def command_scan(config_path: Path, output_root: Path) -> list[Candidate]:
    config = load_config(config_path)
    input_path = resolve_config_path(config["input"], config_path)
    configured_input = Path(config["input"])
    if not configured_input.is_absolute():
        configured_input = (config_path.parent / configured_input).absolute()
    input_label = portable_repo_path(configured_input)
    forbidden = config["selection"]["forbidden_proof_tokens"]
    candidates = [
        extract_candidate(record, Path(input_label), forbidden)
        for record in iter_jsonl(input_path)
    ]
    policy = config["selection"]
    selected = select_candidates(candidates, int(config["sample_size"]), policy)
    policy_eligible = [item for item in candidates if candidate_matches_policy(item, policy)]
    seed = str(policy.get("seed") or "")
    output_root.mkdir(parents=True, exist_ok=True)
    write_json(output_root / "candidate_audit.json", {
        "schema_version": "dependency_graph_candidate_audit_v2",
        "input": input_label,
        "total_records": len(candidates),
        "base_eligible": sum(item.eligible for item in candidates),
        "policy_eligible": len(policy_eligible),
        "selection": {
            "strategy": policy.get("strategy"),
            "seed": seed or None,
            "sample_size": int(config["sample_size"]),
            "population_by_structural_stratum": dict(sorted(Counter(
                candidate_stratum(item, policy) for item in policy_eligible
            ).items())),
            "selected_by_structural_stratum": dict(sorted(Counter(
                candidate_stratum(item, policy) for item in selected
            ).items())),
        },
        "selected": [{
            **item.summary(),
            "structural_stratum": candidate_stratum(item, policy),
            "hash_rank": candidate_hash_rank(item, seed) if seed else None,
        } for item in selected],
        "rejection_reason_counts": dict(sorted(
            (reason, sum(reason in item.rejection_reasons for item in candidates))
            for reason in {reason for item in candidates for reason in item.rejection_reasons}
        )),
    })
    return selected


def command_all(
    config_path: Path,
    output_root: Path,
    skip_lean: bool = False,
    force_lean: bool = False,
) -> None:
    config = load_config(config_path)
    selected = command_scan(config_path, output_root)
    candidate_root = output_root / "candidates"
    entries = [write_candidate_artifacts(item, candidate_root) for item in selected]
    if not skip_lean:
        run_lean_exporter(
            entries,
            output_root,
            force=force_lean,
            batch_size=int((config.get("lean") or {}).get("batch_size", 20)),
        )
    graphs: list[dict[str, Any]] = []
    graph_root = output_root / "graphs"
    for candidate, entry in zip(selected, entries, strict=True):
        raw_path = Path(entry["raw_graph"])
        if not raw_path.is_file():
            raise FileNotFoundError(f"missing raw Lean graph: {raw_path}")
        raw = json.loads(raw_path.read_text(encoding="utf-8"))
        graph_dir = graph_root / candidate.slug
        graph_dir.mkdir(parents=True, exist_ok=True)
        theorem_rows = raw.get("theorems") or []
        if len(theorem_rows) != 1:
            raise ValueError(
                f"expected exactly one theorem row in {raw_path}; found {len(theorem_rows)}"
            )
        actual_export_theorem_name = str(theorem_rows[0].get("theorem_name") or "")
        graph = project_graph(
            candidate,
            raw,
            str(Path("../../candidates") / candidate.slug / "proof.lean"),
            str(Path("../../candidates") / candidate.slug / "raw_graph.json"),
            actual_export_theorem_name,
        )
        graphs.append(graph)
    topology_batch = write_topology_certificates(graphs, graph_root, output_root)
    run_topology_lean_check(graphs, topology_batch, output_root)
    install_concrete_semantic_certificates(graphs, graph_root)
    run_concrete_semantic_lean_checks(
        graphs,
        output_root,
        batch_size=int(
            (config.get("lean") or {}).get("semantic_certificate_batch_size", 20)
        ),
    )
    for graph in graphs:
        graph_dir = graph_root / graph["graph_id"]
        write_json(graph_dir / "graph.json", graph)
        render_svg(graph, graph_dir / "graph.svg")
        render_dot(graph, graph_dir / "graph.dot")
        render_markdown(graph, graph_dir / "graph.md")
    distributions = {
        "selected_depth": dict(sorted(Counter(
            str(graph["metrics"]["selected_depth"]) for graph in graphs
        ).items(), key=lambda item: int(item[0]))),
        "selected_hyperedge_count": dict(sorted(Counter(
            str(graph["metrics"]["selected_hyperedge_count"]) for graph in graphs
        ).items(), key=lambda item: int(item[0]))),
        "max_fan_in_all": dict(sorted(Counter(
            str(graph["metrics"]["max_fan_in_all"]) for graph in graphs
        ).items(), key=lambda item: int(item[0]))),
        "excluded_info_tree_binding_count": dict(sorted(Counter(
            str(graph["metrics"]["excluded_info_tree_binding_count"]) for graph in graphs
        ).items(), key=lambda item: int(item[0]))),
        "axiom_status": dict(sorted(Counter(
            graph["axiom_audit"]["status"] for graph in graphs
        ).items())),
    }
    write_json(output_root / "summary.json", {
        "schema_version": "dependency_graph_cohort_summary_v2",
        "graph_count": len(graphs),
        "lean_version": "4.29.0",
        "selection_strategy": config["selection"].get("strategy"),
        "selection_seed": config["selection"].get("seed"),
        "distributions": distributions,
        "graphs": [{
            "graph_id": graph["graph_id"],
            "theorem_name": graph["task"]["theorem_name"],
            "problem_idx": graph["task"]["problem_idx"],
            "metrics": graph["metrics"],
            "validation": graph["validation"],
        } for graph in graphs],
    })
    write_index(graphs, output_root)
    write_cohort_report(graphs, output_root, config, distributions)
    normalize_json_tree(output_root)
    command_validate(
        config_path, output_root, quiet=True, recheck_concrete=False
    )
    print(f"wrote {len(graphs)} graphs to {graph_root}")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("scan", "all", "validate"), nargs="?", default="all")
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--skip-lean", action="store_true", help="reuse existing raw_graph.json files")
    parser.add_argument("--force-lean", action="store_true", help="ignore valid raw-graph cache entries")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    config_path = args.config.resolve()
    output_root = args.output.resolve()
    if args.skip_lean and args.force_lean:
        raise SystemExit("--skip-lean and --force-lean cannot be used together")
    if args.command == "scan":
        selected = command_scan(config_path, output_root)
        for item in selected:
            print(json.dumps(item.summary(), ensure_ascii=False))
    elif args.command == "validate":
        command_validate(config_path, output_root)
    else:
        command_all(
            config_path,
            output_root,
            skip_lean=args.skip_lean,
            force_lean=args.force_lean,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
