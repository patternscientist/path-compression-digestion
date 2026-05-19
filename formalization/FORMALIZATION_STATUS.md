# Formalization Status

This document records the current boundary between the paper/proof-note packet
and the Lean formalization lane. It is a status note, not a theorem statement
and not a claim of full formalization of the Seidel--Sharir recurrence.

## Paper/proof-note layer

The publication-facing mathematical packet is the v2.2 proof note:

- `proof_note/path_compression_v2_2_integrated_proof_note_public_packaging.md`

The packaging layer tracked here is the v0.1.4 packaging-cleanup release. At
this layer, the target comparison remains

```text
R_{z+1}(Q) >= A(z,4Q)
```

with

```text
Q(m,n) = ceil(1 + m/n)
L(n) = ceil(log_2 max(n,2))
c = 1, C = 1, D = 4
```

## Current Lean layer

The Lean project in `formalization/lean/` formalizes an abstract threshold
engine. It does not define the concrete Seidel--Sharir `J` hierarchy, the
`diamond` operator, or the concrete maximum-defined inverse
`R_k(t) = max { r >= 0 : J_k(r) <= t }`.

The main Lean boundary is:

```lean
ThresholdCoreAssumptions R
```

The comparison results are proved for any abstract threshold family `R`
satisfying those assumptions.

## Proved in Lean

- Packet Ackermann package in
  `formalization/lean/PathCompressionDigestion/Ackermann.lean`.
- Threshold jump from `ThresholdCoreAssumptions` in
  `formalization/lean/PathCompressionDigestion/Threshold.lean`.
- Main comparison from `ThresholdCoreAssumptions` in
  `formalization/lean/PathCompressionDigestion/MainComparison.lean`.

In particular, the abstract theorem currently built by Lean is the conditional
comparison

```lean
forall z Q, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q
```

under `ThresholdCoreAssumptions R`.

## Not Yet Proved in Lean

- The concrete `J` hierarchy.
- The `diamond` operator and its termination/properties.
- The concrete maximum-defined inverse `R_k(t)`.
- The proof that the concrete `R` satisfies `ThresholdCoreAssumptions`.
- The alpha definitions and cost consequences.

## Build Check

From `formalization/lean/`:

```powershell
lake build
```

The GitHub Actions workflow `.github/workflows/lean-formalization.yml` runs
this build lane using the toolchain pinned by
`formalization/lean/lean-toolchain`.
