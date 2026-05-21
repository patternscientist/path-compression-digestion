# Concrete Bridge Roadmap

This roadmap records the remaining concrete Lean bridge from the current main
checkpoint to the concrete main comparison theorem. It is a coordination note,
not a theorem statement, and it does not claim that the concrete threshold
inverse `R` or `Abstract.ThresholdCoreAssumptions R` has already been
formalized.

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

Complete and trusted for the concrete bridge:

- `Diamond`: complete. The reusable `DiamondInput` transform and its
  preservation package are proved in `PathCompressionDigestion/Diamond.lean`.
- `JHierarchy`: complete. The recursive concrete `J_k` hierarchy and the
  basic package of monotonicity, unboundedness, descent, successor-row bound,
  and level antitonicity are proved in
  `PathCompressionDigestion/JHierarchy.lean`.
- `ThresholdInverseExtras`: complete. The generic constructor and escape
  lemmas for finite threshold inverses are proved in
  `PathCompressionDigestion/ThresholdInverseExtras.lean`.
- `AlphaPrelude`: complete only as generic/preparatory infrastructure. It does
  not formalize the paper-specific `alpha_Q`, `alpha_J^Q`, `alpha_J^S`, or the
  cost theorem.
- Theorem map/docs: complete as the current worker coordination layer. The
  docs identify the abstract comparison theorem to reuse and the concrete
  threshold/core work still open.

The abstract Lean comparison stack is also available: after a future concrete
family satisfies `Abstract.ThresholdCoreAssumptions R`,
`Abstract.main_comparison_from_core` supplies the comparison theorem.

## 2. Next Concrete-R Branch

Target file:

```text
PathCompressionDigestion/ConcreteThreshold.lean
```

Purpose: define the concrete threshold inverse family from the already proved
`J` hierarchy, using the generic threshold-inverse infrastructure instead of
hand-rolling a finite maximum.

Required definitions/theorems:

- `JThresholdData`: package each row `J k` as `ThresholdInverse.Data`, using
  `J_zero_arg`, `J_monotone`, and `J_unbounded`.
- `R` or `concreteR`: define the concrete inverse family by
  `ThresholdInverse.thresholdInverse (JThresholdData k) t`.
- `R_zero_eq`: prove the base row is exact, using the existing `JBase` inverse
  facts, with target shape `R 0 t = 2 * t + 1`.
- `R_monotone_threshold`: prove monotonicity of `R k` in the threshold
  argument from the generic inverse monotonicity theorem.
- `R_monotone_level`: prove `R k t <= R (k + 1) t` from
  `J_succ_le` and the generic function-comparison inverse theorem.
- `J_R_le`: prove the forward max fact `J k (R k t) <= t`.
- `le_R_of_J_le`: prove maximality, `J k r <= t -> r <= R k t`.
- `lt_J_of_R_lt`: prove the strict contrapositive escape lemma,
  `R k t < r -> t < J k r`.

This branch must not claim the threshold step or
`Abstract.ThresholdCoreAssumptions R`; it only builds the concrete inverse
API.

## 3. Generic Diamond-Threshold Support Branch

Target file:

```text
PathCompressionDigestion/DiamondThreshold.lean
```

Required theorem:

```text
generic inverse recurrence for a DiamondInput D:
  Rg (2 ^ Rh t) <= Rh (t + 1)
```

Here `g` is the input row packaged by `D`, `h = D.diamond`, `Rg` is the
threshold inverse for `g`, and `Rh` is the threshold inverse for `h`.

Proof sketch:

- Set `r = Rg (2 ^ Rh t)`.
- Use the inverse spec for `Rg` to get `D.g r <= 2 ^ Rh t`.
- Split on `D.g r <= 1`.
- Small branch: use the diamond small equation to get
  `D.diamond r = D.g r <= 1 <= t + 1`.
- Large branch: use the diamond large equation, the `ceilLog2` upper bound from
  `D.g r <= 2 ^ Rh t`, diamond monotonicity, and the inverse spec for `Rh` to
  show `D.diamond r <= t + 1`.
- Conclude `r <= Rh (t + 1)` by maximality of `Rh`.

This file should remain generic over `DiamondInput`; the concrete `J` branch
can instantiate it later for `D = JInput k`.

## 4. Concrete Core Branch After A/B Merge

Target file:

```text
PathCompressionDigestion/ConcreteCore.lean
```

Required theorem:

```lean
Abstract.ThresholdCoreAssumptions R
```

Required fields:

- base exactness: from `R_zero_eq`;
- threshold monotonicity: from `R_monotone_threshold`;
- level monotonicity: from `R_monotone_level`;
- threshold step: from the generic diamond-threshold recurrence instantiated
  with `D = JInput k`, giving
  `R k (2 ^ (R (k + 1) t)) <= R (k + 1) (t + 1)`.

This is the first branch allowed to claim the concrete threshold family
satisfies the abstract core assumptions.

## 5. Concrete Main Comparison Corollary

After `ConcreteCore.lean` proves `Abstract.ThresholdCoreAssumptions R`, the
concrete main comparison should be a corollary obtained by applying:

```lean
Abstract.main_comparison_from_core
```

Do not re-prove the abstract comparison, row-domination invariant, small
`Q = 1` case, or threshold jump. Those are already proved abstractly from the
core interface.

## 6. Remaining Alpha/Cost Tail

Later work, after the concrete main comparison corollary:

- paper-specific `L(n)` and `Q(m,n)`;
- concrete `alpha_Q`, `alpha_J^Q`, and `alpha_J^S`;
- the `+1/+2` alpha consequences;
- the source recurrence/cost theorem.

`AlphaPrelude.lean` only provides generic least-index and Ackermann-buffer
preparation for this later tail.

## 7. Validation Policy

- Lean source branches must run targeted module checks and source-only
  no-sorry scans.
- Docs-only branches should run `git diff --check` and the source-only
  no-sorry scan.
- Do not force a full Mathlib rebuild unless preparing a release.

For this docs-only roadmap branch, do not run `lake build` or any command that
can rebuild Mathlib.
