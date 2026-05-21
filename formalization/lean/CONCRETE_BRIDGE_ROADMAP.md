# Concrete Bridge Roadmap

This roadmap records the remaining concrete Lean bridge after the successful
merges of `lean-concrete-threshold-v1` and
`lean-diamond-threshold-step-v1`. It is a coordination note, not a theorem
statement, and it does not claim that the concrete
`ThresholdCoreAssumptions R`, concrete main comparison corollary, or
paper-specific alpha/cost theorem has already been formalized.

The comparison target remains:

```text
R_{z+1}(Q) >= A(z,4Q)
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
```

Any change touching these normalizations or constants should be treated as
high risk.

## 1. Current Trusted Lean Stack

Complete and trusted for the next concrete bridge:

- `Diamond`: complete. `PathCompressionDigestion/Diamond.lean` proves the
  reusable `DiamondInput` transform and preservation package.
- `JHierarchy`: complete. `PathCompressionDigestion/JHierarchy.lean` defines
  the recursive concrete `J_k` hierarchy and proves the basic row package.
- `ThresholdInverseExtras`: complete.
  `PathCompressionDigestion/ThresholdInverseExtras.lean` provides the generic
  constructor and escape lemmas used by concrete threshold inverses.
- `ConcreteThreshold` / concrete `R`: complete.
  `PathCompressionDigestion/ConcreteThreshold.lean` defines the concrete
  maximum-style threshold inverse for `J`.
- `DiamondThreshold` / generic diamond-to-threshold recurrence: complete.
  `PathCompressionDigestion/DiamondThreshold.lean` proves the generic
  recurrence for a `DiamondInput` row and its diamond transform.
- `AlphaPrelude`: complete only as generic/preparatory infrastructure. It does
  not formalize the paper-specific `alpha_Q`, `alpha_J^Q`, `alpha_J^S`, or the
  cost theorem.
- Theorem map/docs: complete as worker coordination notes for the current
  bridge boundary.

The abstract comparison stack is also available. Once the concrete `R`
satisfies `ThresholdCoreAssumptions R`, the comparison should be obtained from
`main_comparison_from_core`.

## 2. ConcreteThreshold Status

Complete in `PathCompressionDigestion/ConcreteThreshold.lean`:

- `JThresholdData`: packages each concrete row `J k` as
  `ThresholdInverse.Data`.
- concrete `R`: defines `R k t` as
  `ThresholdInverse.thresholdInverse (JThresholdData k) t`.
- base exactness: `R_zero_eq`, proving `R 0 t = 2 * t + 1`.
- threshold monotonicity: `R_monotone_threshold`, plus the pointwise wrapper
  `R_mono_t`.
- level monotonicity: `R_monotone_level`, proving
  `R k t <= R (k + 1) t`.
- concrete inverse/spec wrappers:
  `J_R_le`, `le_R_of_J_le`, and `lt_J_of_R_lt`.

This file does not prove `ThresholdCoreAssumptions R`; the threshold-step field
is supplied by the next concrete-core bridge.

## 3. DiamondThreshold Status

Complete in `PathCompressionDigestion/DiamondThreshold.lean`:

- generic inverse data for a `DiamondInput` row:
  `DiamondInput.gThresholdData`;
- generic inverse data for its diamond transform:
  `DiamondInput.diamondThresholdData`;
- generic inverse families:
  `DiamondInput.Rg` and `DiamondInput.Rdiamond`;
- generic recurrence:

```text
Rg (2 ^ Rdiamond t) <= Rdiamond (t + 1)
```

in Lean as:

```lean
DiamondInput.threshold_step
```

This theorem remains generic over `DiamondInput`; the concrete core branch
should specialize it to `JInput k`.

## 4. Next Critical Branch: ConcreteCore

Target file:

```text
formalization/lean/PathCompressionDigestion/ConcreteCore.lean
```

Required theorem:

```lean
ThresholdCoreAssumptions R
```

or, with the current namespace made explicit:

```lean
Abstract.ThresholdCoreAssumptions R
```

Required fields:

- base exactness: from `R_zero_eq`;
- threshold monotonicity: from `R_monotone_threshold`;
- level monotonicity: from `R_monotone_level`;
- threshold step: from `DiamondInput.threshold_step` specialized to
  `JInput k`.

Expected proof sketch for the threshold-step field:

- unfold concrete `R`;
- identify `R k` with `DiamondInput.Rg (JInput k)`;
- identify `R (k + 1)` with `DiamondInput.Rdiamond (JInput k)`, using
  `J_succ_row` and `DiamondInput.next`;
- apply `DiamondInput.threshold_step`.

This branch is the first one that should claim the concrete threshold family
satisfies the abstract core assumptions.

## 5. After ConcreteCore

Later work after `ConcreteCore.lean` proves `ThresholdCoreAssumptions R`:

- concrete main comparison corollary using `main_comparison_from_core`;
- paper consequence `A z (4*Q) > r -> J (z+1) r <= Q`;
- paper-specific alpha definitions and the `+1/+2` consequences;
- source recurrence/cost theorem.

Do not re-prove the abstract comparison when instantiating the concrete
corollary; reuse the abstract theorem.

## 6. Parallel Worktree Coordination

Multiple Codex Pro chats can work in separate worktrees at the same time, and
the roadmap should use that when it shortens the critical path without creating
coordination churn.

Good parallel splits have clear ownership and low coupling. For example, after
the concrete core theorem lands, one worktree can package the concrete main
comparison corollary while another prepares paper-specific alpha/cost docs or
scaffolding, as long as neither branch edits the same Lean modules or claims
results that depend on unmerged work.

Do not split a task merely because parallelism is available. The next
`ConcreteCore.lean` bridge is tightly coupled around identifying concrete `R`
with the generic diamond-threshold inverses, so it is probably best handled by
one chat unless a worker is assigned a genuinely independent audit or docs
update.

Each parallel branch should record:

- base commit and dependency branch, if any;
- owned files/modules;
- theorem or documentation boundary;
- validation actually run;
- claims intentionally left open.

## 7. Validation Policy

- Docs-only branches: run `git diff --check` and the source-only no-sorry scan.
- Lean branches: run targeted module checks and the source-only no-sorry scan.
- Do not force full Mathlib rebuilds for every branch.

For docs-only roadmap work, do not run `lake build` or any command that can
rebuild Mathlib.
