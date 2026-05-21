# Concrete Bridge Status and Roadmap

This roadmap records the concrete Lean bridge after the successful merges of
`lean-concrete-threshold-v1`, `lean-diamond-threshold-step-v1`, and
`lean-concrete-core-v1`. It is a coordination note, not a theorem statement.
The concrete `ThresholdCoreAssumptions R` package and concrete main comparison
are now present; the paper-specific alpha/cost theorem and source recurrence
remain outside the current Lean stack.

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

Complete and trusted after the concrete bridge:

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
- `ConcreteCore`: complete.
  `PathCompressionDigestion/ConcreteCore.lean` proves the concrete threshold
  core assumptions for `R` and the concrete main comparison via
  `Abstract.main_comparison_from_core`.
- `AlphaPrelude`: complete only as generic/preparatory infrastructure. It does
  not formalize the paper-specific `alpha_Q`, `alpha_J^Q`, `alpha_J^S`, or the
  cost theorem.
- Theorem map/docs: complete as worker coordination notes for the current
  bridge boundary.

The abstract comparison stack is also available. The concrete `R` now satisfies
`ThresholdCoreAssumptions R`, and the comparison is obtained from
`Abstract.main_comparison_from_core`.

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

This file does not itself prove `ThresholdCoreAssumptions R`; that package is
proved in `ConcreteCore.lean` using these facts and the generic
diamond-to-threshold recurrence.

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

This theorem remains generic over `DiamondInput`; `ConcreteCore.lean`
specializes it to `JInput k`.

## 4. ConcreteCore Status

Complete in:

```text
formalization/lean/PathCompressionDigestion/ConcreteCore.lean
```

Concrete inverse identifications:

```lean
R_eq_Rg_JInput
R_succ_eq_Rdiamond_JInput
```

Concrete threshold core package:

```lean
concrete_threshold_core_assumptions :
  Abstract.ThresholdCoreAssumptions R
```

Concrete main comparison via the abstract theorem:

```lean
concrete_main_comparison :
  forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q
```

## 5. After ConcreteCore

Later work after the landed concrete core:

- paper consequence `A z (4*Q) > r -> J (z+1) r <= Q`;
- paper-specific `L(n)`, `Q(m,n)`, `alpha_Q`, `alpha_J^Q`, `alpha_J^S`, and
  the `+1/+2` comparisons;
- source recurrence/cost theorem.
- full paper-facing formalization of the final top-down compression bound.

Do not claim paper-specific alpha/cost consequences, the source
recurrence/cost theorem, or the full final compression bound from
`ConcreteCore.lean` alone.

## 6. Parallel Worktree Coordination

Multiple Codex Pro chats can work in separate worktrees at the same time, and
the roadmap should use that when it shortens the critical path without creating
coordination churn.

Good parallel splits have clear ownership and low coupling. For example, one
worktree can package the direct paper consequence while another prepares
paper-specific alpha/cost docs or scaffolding, as long as neither branch edits
the same Lean modules or claims results that depend on unmerged work.

Do not split a task merely because parallelism is available. The next
paper-specific steps depend on precise normalization choices, so each branch
should keep its theorem boundary narrow unless a worker is assigned a genuinely
independent audit or docs update.

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
