# Codex Prompt: Dependency DAG

Read `AGENTS.md`.

Do not alter the proof note.

Task:
Build a proof-digestion dependency map from:

```text
proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md
```

Produce:

1. `audits/dependency_table.md` with columns:
   - label
   - statement summary
   - depends on
   - used by
   - status: source / proved / derived / explanatory / needs human review

2. `audits/proof_dependency_dag.mmd` as a Mermaid DAG showing the route:

```text
Seidel--Sharir source recurrence
  -> J hierarchy
  -> R threshold recurrence
  -> Ackermann comparison
  -> alpha_Q / alpha_J comparison
  -> final path-compression bound
```

If dependencies are ambiguous, mark them as `needs human review` rather than guessing.
