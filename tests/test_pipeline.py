from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import pipeline  # noqa: E402


def candidate(
    idx: int, *, tokens: int, helper_count: int, have_count: int = 2
) -> pipeline.Candidate:
    return pipeline.Candidate(
        problem_idx=idx,
        unique_id=f"candidate-{idx}",
        source="paper",
        model="model",
        token_count=tokens,
        theorem_name=f"theorem_{idx}",
        formal_statement=f"theorem theorem_{idx} : True := by trivial",
        submission=f"theorem theorem_{idx} : True := by trivial",
        helpers=["lemma helper : True := by trivial"] * helper_count,
        retrieval_events=[pipeline.RetrievalEvent("search:1", "loogle", "True", [], 0, 1)],
        verification_call_id="verify:1",
        verification_result="### Compiles ###\nTrue\n### Valid Proof ###\nTrue",
        main_have_count=have_count,
        accepted_helper_count=helper_count,
        tool_call_count=2,
        source_file="rollouts.jsonl",
    )


class PipelineUnitTests(unittest.TestCase):
    def test_placeholder_scan_ignores_comments_and_strings(self) -> None:
        source = '''
-- sorry
/- outer axiom /- nested admit -/ end -/
def message : String := "sorry axiom"
theorem bad : True := by sorry
'''
        self.assertEqual(pipeline.forbidden_tokens(source, ["sorry", "admit", "axiom"]), ["sorry"])

    def test_unclosed_command_scope_count_models_lean_eof_closure(self) -> None:
        source = '''
/- section fake -/
noncomputable section
namespace Inner
def message : String := "end Inner"
end Inner
section Named
end Named
theorem result : True := by trivial
'''
        self.assertEqual(pipeline.unclosed_command_scope_count(source), 1)

    def test_batch_source_closes_rollout_section_before_its_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            proof = root / "proof.lean"
            proof.write_text(
                "import Mathlib\nnoncomputable section\n"
                "theorem result : True := by trivial\n",
                encoding="utf-8",
            )
            batch = pipeline.write_batch_source(
                [{"proof": str(proof), "batch_namespace": "Rollout_test"}], root / "batch"
            ).read_text(encoding="utf-8")
        self.assertIn(
            "theorem result : True := by trivial\n\n"
            "/- Scopes closed implicitly by EOF in the original file. -/\n"
            "end\n\nend Rollout_test",
            batch,
        )

    def test_tool_calls_pair_by_id_not_position(self) -> None:
        conversation = [
            {"role": "assistant", "tool_calls": [
                {"id": "a", "name": "loogle", "arguments": {"query": "x"}},
                {"id": "b", "name": "verify_submission", "arguments": {"code": "proof"}},
            ]},
            {"role": "tool", "tool_call_id": "b", "content": "verified"},
            {"role": "tool", "tool_call_id": "a", "content": "search result"},
        ]
        events = {event.call_id: event for event in pipeline.pair_tool_events(conversation)}
        self.assertEqual(events["a"].result, "search result")
        self.assertEqual(events["b"].result, "verified")
        self.assertEqual(events["a"].result_turn, 2)

    def test_retrieval_declaration_parser(self) -> None:
        result = "1. Nat.add_comm\n2. [0] Real.exp_pos\n- Finset.sum_const : statement"
        self.assertEqual(
            pipeline.parse_retrieved_declarations(result),
            ["Nat.add_comm", "Real.exp_pos", "Finset.sum_const"],
        )

    def test_stratified_selection_respects_helper_quotas(self) -> None:
        items = [
            candidate(1, tokens=20, helper_count=0),
            candidate(2, tokens=10, helper_count=0),
            candidate(3, tokens=15, helper_count=1),
            candidate(4, tokens=30, helper_count=1),
        ]
        policy = {
            "min_main_have_count": 1,
            "max_main_have_count": 10,
            "max_submission_chars": 1000,
            "require_retrieval_event": True,
            "no_helper_quota": 1,
            "with_helper_quota": 1,
        }
        selected = pipeline.select_candidates(items, 2, policy)
        self.assertEqual([item.problem_idx for item in selected], [2, 3])

    def test_hash_selection_is_deterministic_and_not_token_sorted(self) -> None:
        items = [
            candidate(1, tokens=1, helper_count=0),
            candidate(2, tokens=2, helper_count=0),
            candidate(3, tokens=3, helper_count=0),
            candidate(4, tokens=4, helper_count=0),
        ]
        policy = {
            "strategy": "deterministic_hash_sample",
            "seed": "unit-test-seed",
            "min_main_have_count": 1,
            "max_main_have_count": 10,
            "max_submission_chars": 1000,
            "require_retrieval_event": True,
        }
        first = pipeline.select_candidates(items, 3, policy)
        second = pipeline.select_candidates(list(reversed(items)), 3, policy)
        self.assertEqual([item.unique_id for item in first], [item.unique_id for item in second])
        self.assertEqual(
            [item.unique_id for item in first],
            sorted(
                (item.unique_id for item in items),
                key=lambda uid: hashlib.sha256(f"unit-test-seed\0{uid}".encode()).hexdigest(),
            )[:3],
        )

    def test_imports_are_removed_from_batch_member(self) -> None:
        source = "import Mathlib\n\nimport Mathlib.Data.Nat.Basic\ntheorem t : True := by trivial\n"
        embedded = pipeline.without_import_commands(source)
        self.assertNotIn("import ", embedded)
        self.assertIn("theorem t", embedded)

    def test_direct_dependency_metrics(self) -> None:
        nodes = {
            "m": {"id": "m", "origin": "manifest", "class": "main"},
            "h": {"id": "h", "origin": "derived", "class": "main"},
            "g": {"id": "g", "origin": "goal", "class": "main"},
        }
        retrieval = {"matched_rule_items": [], "observed_search_event_ids": []}
        edges = [
            {"id": "eh", "selected": True, "class": "main", "premises": ["m"], "conclusion": "h", "retrieval": retrieval},
            {"id": "eg", "selected": True, "class": "main", "premises": ["h"], "conclusion": "g", "retrieval": retrieval},
        ]
        result = pipeline.validate_and_measure(nodes, edges, "g")
        self.assertTrue(result["goal_reachable"])
        self.assertTrue(result["acyclic"])
        self.assertEqual(result["metrics"]["selected_depth"], 2)
        self.assertEqual(result["metrics"]["max_fan_in_all"], 1)

    def test_topology_certificate_composes_exact_selected_closure(self) -> None:
        graph = {
            "graph_id": "unit_graph",
            "task": {"goal_node": "g"},
            "nodes": [
                {"id": "m", "selected": True, "binding_name": "hm", "statement": "P"},
                {"id": "h", "selected": True, "binding_name": "hh", "statement": "Q"},
                {"id": "g", "selected": True, "binding_name": "goal", "statement": "R"},
            ],
            "hyperedges": [
                {"id": "e1", "selected": True, "premises": ["m"], "conclusion": "h"},
                {"id": "e2", "selected": True, "premises": ["h"], "conclusion": "g"},
            ],
        }
        source = pipeline.topology_certificate_source(graph)
        self.assertIn("theorem graph_derives_goal", source)
        self.assertIn("have H_N002 : N002 := E001 B001", source)
        self.assertIn("have H_N003 : N003 := E002 H_N002", source)
        self.assertIn("exact H_N003", source)
        self.assertEqual(len(pipeline.topology_fingerprint(graph)), 64)

    def test_p1662_concrete_certificate_matches_every_selected_edge(self) -> None:
        graph_path = (
            ROOT / "outputs" / "random100" / "graphs"
            / "p1662_binary_quadratic_form_volume_identity" / "graph.json"
        )
        graph = json.loads(graph_path.read_text(encoding="utf-8"))
        certificate = pipeline.concrete_semantic_certificate_source(graph)
        proof_path = (
            graph_path.parent / graph["sources"]["reconstructed_proof"]
        ).resolve()
        self.assertEqual(
            pipeline.concrete_semantic_certificate_errors(
                graph, certificate, proof_path
            ),
            [],
        )
        self.assertIn("Generated exact graph/type bridge", certificate)
        self.assertIn(
            "P1662ConcreteSemanticGraph.edge_h_006_hmu_at_one "
            "(a := a) (b := b) (c := c) P001",
            certificate,
        )
        tampered = certificate.replace(
            "theorem edge_h_006_hmu_at_one",
            "theorem edge_h_006_wrong_edge",
            1,
        )
        errors = pipeline.concrete_semantic_certificate_errors(
            graph, tampered, proof_path
        )
        self.assertTrue(any("edge theorem ids differ" in error for error in errors))

    def test_generic_certificate_embeds_proof_and_exact_manifest(self) -> None:
        graph_path = (
            ROOT / "outputs" / "random100" / "graphs"
            / "p0109_exists_atomic_puiseux_monoid_without_singl" / "graph.json"
        )
        graph = json.loads(graph_path.read_text(encoding="utf-8"))
        proof_path = (
            graph_path.parent / graph["sources"]["reconstructed_proof"]
        ).resolve()
        source = pipeline.concrete_semantic_certificate_source(graph, proof_path)
        spec = pipeline.concrete_semantic_replay_spec(graph, proof_path)
        self.assertEqual(spec["selectedEdgeCount"], 1)
        self.assertEqual(spec["edges"][0]["rawEdgeId"], "goal_edge")
        self.assertEqual(spec["edges"][0]["graphEdgeId"], "h_goal")
        self.assertIn("-- certificate_kind: embedded_theorem_replay", source)
        self.assertIn("#check_dependency_graph", source)
        self.assertIn("/- verified submission -/", source)
        self.assertEqual(
            pipeline.concrete_semantic_certificate_errors(
                graph, source, proof_path
            ),
            [],
        )

    def test_generated_internal_binder_path_is_canonicalized(self) -> None:
        graph_dir = (
            ROOT / "outputs" / "graphs"
            / "p1572_not_biorderable_of_product_conjugates_eq_o"
        )
        graph = json.loads((graph_dir / "graph.json").read_text(encoding="utf-8"))
        proof_path = (
            graph_dir / graph["sources"]["reconstructed_proof"]
        ).resolve()
        spec = pipeline.concrete_semantic_replay_spec(graph, proof_path)
        premises = [
            premise
            for edge in spec["edges"]
            for premise in edge["premises"]
        ]

        self.assertTrue(any(
            premise["name"] == "<generated-internal>" for premise in premises
        ))
        self.assertFalse(any(
            "._@._internal." in premise["name"] for premise in premises
        ))

    def test_persisted_paths_are_repository_relative(self) -> None:
        artifact = ROOT / "outputs" / "example.json"
        rendered = pipeline.portable_json_value({
            "source": str(artifact),
            "diagnostic": f"{artifact}:1: warning",
        })

        self.assertEqual(rendered["source"], "outputs/example.json")
        self.assertEqual(
            rendered["diagnostic"], "outputs/example.json:1: warning"
        )
        self.assertEqual(
            pipeline.resolve_recorded_path(rendered["source"]), artifact
        )

    def test_raw_graph_cache_is_invalidated_by_proof_change(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proof = root / "proof.lean"
            source = root / "batch.lean"
            raw = root / "raw.json"
            proof.write_text("theorem cached : True := by trivial\n", encoding="utf-8")
            source.write_text("import Mathlib\n", encoding="utf-8")
            proof_hash = hashlib.sha256(proof.read_bytes()).hexdigest()
            pipeline.write_json(raw, {
                "schema_version": "lean_proof_term_projection_raw_v4",
                "lean_version": "4.29.0",
                "theorems": [{"theorem_name": "Rollout.cached"}],
                "batch_provenance": {
                    "source": str(source),
                    "namespace": "Rollout",
                    "isolation_mode": "generated_namespace_batch",
                    "export_theorem_name": "Rollout.cached",
                    "proof_sha256": proof_hash,
                },
            })
            entry = {
                "proof": str(proof),
                "raw_graph": str(raw),
                "export_theorem_name": "Rollout.cached",
                "theorem_name": "cached",
            }
            self.assertTrue(pipeline.raw_graph_cache_valid(entry))
            proof.write_text("theorem cached : True := by exact True.intro\n", encoding="utf-8")
            self.assertFalse(pipeline.raw_graph_cache_valid(entry))

    def test_standalone_export_name_is_a_valid_cache_variant(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proof = root / "proof.lean"
            exporter_raw = root / "exporter.json"
            cached_raw = root / "cached.json"
            proof.write_text("theorem cached : True := by trivial\n", encoding="utf-8")
            pipeline.write_json(exporter_raw, {
                "schema_version": "lean_proof_term_projection_raw_v4",
                "lean_version": "4.29.0",
                "theorems": [{"theorem_name": "cached"}],
                "local_edges": [],
                "excluded_local_bindings": [],
            })
            entry = {
                "slug": "cached",
                "proof": str(proof),
                "raw_graph": str(cached_raw),
                "theorem_name": "cached",
                "export_theorem_name": "Rollout.cached",
            }
            pipeline.save_standalone_raw_graph(entry, exporter_raw, proof)
            self.assertTrue(pipeline.raw_graph_cache_valid(entry))
            cached = json.loads(cached_raw.read_text(encoding="utf-8"))
            self.assertEqual(
                cached["batch_provenance"]["isolation_mode"], "standalone_source"
            )


if __name__ == "__main__":
    unittest.main()
