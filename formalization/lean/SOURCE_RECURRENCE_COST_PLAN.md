# Source Recurrence / Cost Theorem Scout

Branch: `source-recurrence-cost-scout-v1`

Starting checkpoint: `5510336cb08543e083b201429e096cdbfbfc1b01`

This is a scouting/design note only. It does not claim that the source
recurrence or final cost theorem is proved in Lean.

## 1. Exact paper theorem

The paper has two relevant source/cost statements.

First, the source recurrence consequence recorded from Seidel--Sharir is:

```text
f(m,n,r) <= k*m + 2*n*J_k(r).
```

In `paper/main.tex`, this appears in the source setup around the shifting
lemma and recurrence consequence:

```text
If f(m,n,r) <= k*m + 2*n*g(r),
then f(m,n,r) <= (k+1)*m + 2*n*g^diamond(r).

Iterating this lemma through the J hierarchy gives:
f(m,n,r) <= k*m + 2*n*J_k(r).
```

Second, the paper-facing cost theorem is Theorem "Cost consequence":

```text
Using the source recurrence f(m,n,r) <= k*m + 2*n*J_k(r), one obtains

f(m,n,L(n)) <= (alphaQ(m,n)+3)*m + 4*n.

Consequently,

f(m,n,L(n)) = O(m*alphaQ(m,n)+n).
```

The theorem's proof uses:

```text
z = alphaQ(m,n)
Q = Q(m,n)
L = L(n)
J_{z+1}(L) <= Q
f(m,n,L) <= (z+1)*m + 2*n*J_{z+1}(L)
             <= (z+1)*m + 2*n*Q
Q <= 2 + m/n
2*n*Q <= 4*n + 2*m
```

Thus the exact finite Lean target should be the arithmetic inequality
`f m n (L n) <= (alphaQ m n + 3) * m + 4 * n`. The asymptotic `O(...)`
sentence can remain documentation until the finite theorem is complete.

## 2. Already formalized

The comparison machinery is already present.

- `A` and Ackermann row facts are in `Ackermann.lean`.
- Concrete `J` is in `JHierarchy.lean`.
- Concrete threshold inverse `R` is in `ConcreteThreshold.lean`.
- The generic diamond-to-threshold step is in `DiamondThreshold.lean`.
- `ConcreteCore.lean` proves:

```lean
concrete_main_comparison :
  forall z Q : Nat, 1 <= z -> 1 <= Q -> A z (4 * Q) <= R (z + 1) Q
```

- `PaperConsequences.lean` proves the direct `J` consequence:

```lean
direct_paper_consequence
    {z Q r : Nat}
    (hz : 1 <= z)
    (hQ : 1 <= Q)
    (hr : A z (4 * Q) > r) :
    J (z + 1) r <= Q
```

- `AlphaTail.lean` defines the first paper-specific alpha layer:

```lean
ceilDiv
L
Q
sourceThreshold
ackermannAlphaFamily
alphaQ
alphaJQ
alphaJS
alphaQExists
```

It also proves conditional packet-alpha bridge lemmas, including:

```lean
alphaQ_spec
alphaJQ_le_succ_of_ackermann_witness
alphaJQ_le_alphaQ_add_one
alphaJS_eq_alphaJQ_of_sourceThreshold_eq_Q
alphaJS_le_alphaQ_add_one_of_sourceThreshold_eq_Q
```

These are enough to avoid reproving the threshold comparison in any future
cost branch.

## 3. Paper symbols still lacking Lean definitions

The following paper symbols or theorem layers are still not Lean definitions
or complete Lean theorems on `main`.

- `f(m,n,r)`: the source path-compression cost functional.
- The source recurrence theorem itself as a Lean theorem about an actual
  data-structure model:

```text
f(m,n,r) <= k*m + 2*n*J_k(r)
```

- The generic source shifting lemma as a cost theorem:

```text
f(m,n,r) <= k*m + 2*n*g(r)
  -> f(m,n,r) <= (k+1)*m + 2*n*g^diamond(r)
```

- `g*`: mentioned in the source setup but not needed for the final cost
  branch if the recurrence is imported as a source assumption.
- `alpha_A(N,X)`: the paper's explanatory classical row inverse. `alphaQ`
  already encodes the needed packet specialization, so a separate definition
  is optional.
- The real-valued expression `1 + m/n` as a rational or real quantity. Current
  Lean uses the Nat threshold `sourceThreshold m n = 1 + m / n`, which is
  correct for Nat-valued `J_k(L(n))` after the standard floor encoding.
- The final source-faithful `alphaJS <= alphaQ + 2` theorem.
- The final finite cost theorem.
- The asymptotic `O(m*alphaQ(m,n)+n)` statement.
- Tarjan's `T_k` and `alpha_T`, intentionally not a dependency.

## 4. Proposed Lean statement

Do not make the next branch a full formalization of path compression. The
smallest source-faithful statement is conditional on a cost family satisfying
the source recurrence.

Suggested file, for a later Lean branch:

```text
formalization/lean/PathCompressionDigestion/SourceCost.lean
```

Suggested interface:

```lean
namespace PathCompressionDigestion

abbrev SourceCostFamily := Nat -> Nat -> Nat -> Nat

structure SourceRecurrence (F : SourceCostFamily) : Prop where
  recurrence :
    forall {k m n r : Nat},
      1 <= m -> 1 <= n ->
      F m n r <= k * m + 2 * n * J k r

theorem source_cost_bound_of_recurrence
    {F : SourceCostFamily}
    (HF : SourceRecurrence F)
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n) :
    F m n (L n) <= (alphaQ m n + 3) * m + 4 * n
```

Before unconditional `alphaQ` existence lands, this theorem should carry an
extra `(hexists : alphaQExists m n)` argument. After the alphaQ-existence branch
lands, the theorem should be stated without that extra assumption.

The proof should use the already-proved direct comparison:

```lean
have hA : L n < A (alphaQ m n) (4 * Q m n) := alphaQ_spec ...
have hJ : J (alphaQ m n + 1) (L n) <= Q m n :=
  direct_paper_consequence
    (one_le_alphaQ m n)
    (one_le_Q m n)
    hA
```

Then apply the source recurrence at `k = alphaQ m n + 1` and `r = L n`.

The remaining arithmetic obligation should be factored into a named lemma:

```lean
theorem two_mul_n_mul_Q_le_two_mul_m_add_four_mul_n
    {m n : Nat} (hn : 1 <= n) :
    2 * n * Q m n <= 2 * m + 4 * n
```

Exact naming can follow the threshold-arithmetic branch once it lands.

## 5. Direct paper quantities or abstract interface?

Use a hybrid.

The alpha and normalization layer should stay direct over the paper quantities:

```lean
L
Q
sourceThreshold
alphaQ
alphaJQ
alphaJS
J
R
```

The cost theorem should be abstract only in the cost functional:

```lean
F : Nat -> Nat -> Nat -> Nat
SourceRecurrence F
```

This avoids pretending that Lean has formalized the Seidel--Sharir data
structure model. It also avoids introducing an `axiom`: the recurrence is a
theorem parameter/interface, and the final theorem is explicitly conditional on
that interface.

Do not push the cost theorem all the way down to
`Abstract.ThresholdCoreAssumptions`. The source recurrence mentions the
concrete `J_k`, not merely an arbitrary inverse family `R`.

## 6. Smallest independent Lean branches after alphaQ existence and threshold arithmetic

After unconditional `alphaQ` existence and the basic `ceilDiv`/threshold
arithmetic have landed, the smallest useful branches are:

1. `lean-alpha-js-real-threshold-v1`

   Prove the full source-faithful comparison:

   ```lean
   alphaJS m n <= alphaQ m n + 2
   ```

   plus the integral-threshold `+1` theorem using the landed threshold
   arithmetic. This branch will likely need the Ackermann buffer lemma:

   ```lean
   A (z + 1) (4 * p) >= A z (4 * p + 4)
   ```

   for `1 <= z` and `1 <= p`.

2. `lean-source-cost-interface-v1`

   Add `SourceCost.lean` with `SourceCostFamily`, `SourceRecurrence`, and the
   finite cost theorem conditional on the source recurrence:

   ```lean
   F m n (L n) <= (alphaQ m n + 3) * m + 4 * n
   ```

   This branch should not define the actual path-compression `f`.

3. `lean-final-paper-wrapper-v1`

   Add a small final theorem wrapper and update `PathCompressionDigestion.lean`,
   `THEOREM_MAP.md`, and `FORMALIZATION_STATUS.md`. The wrapper should assemble:

   - `concrete_main_comparison`;
   - `direct_paper_consequence`;
   - `alphaJQ <= alphaQ + 1`;
   - `alphaJS <= alphaQ + 2`;
   - the conditional source-cost theorem.

   It should still state clearly that the source recurrence is an interface
   assumption unless a later, much larger source-model formalization exists.

## 7. Likely hard proof obligations

- Proving the Ackermann buffer lemma in the packet normalization:

```text
A(z+1,4p) >= A(z,4p+4).
```

- Getting the Nat encoding of the real source threshold exactly right:

```text
sourceThreshold m n = 1 + m / n
Q m n = 1 + ceilDiv m n
sourceThreshold m n = Q m n    iff    n divides m
sourceThreshold m n + 1 = Q m n in the nonintegral case
```

- Proving the cost arithmetic in Nat form without changing constants:

```text
2*n*Q(m,n) <= 2*m + 4*n.
```

- Bridging least-index alpha definitions to concrete `J` facts. Prefer the
  direct route through `direct_paper_consequence` at index `alphaQ m n`; do not
  re-open the threshold comparison proof.
- Maintaining the positive-domain hypotheses for `m,n`. The paper states
  positive integers; the Lean theorem should require `1 <= m` and `1 <= n`
  unless a later branch deliberately generalizes harmless zero cases.
- Avoiding accidental dependence on the non-source-faithful `2*m/n` threshold.

## 8. What not to attempt yet

- Do not formalize the actual Seidel--Sharir path-compression cost function
  `f` yet.
- Do not formalize the rank-forest model, compression sequences, or the proof
  of the source shifting lemma.
- Do not introduce `axiom`, `admit`, or `sorry` for the source recurrence.
- Do not replace the source recurrence with a Tarjan-style potential proof.
- Do not define or compare Tarjan's `T_k` / `alpha_T`.
- Do not change `L`, `Q`, `A`, `J`, `R`, or the constants `c=1`, `C=1`,
  `D=4`.
- Do not formalize the asymptotic `O(...)` statement before the finite cost
  inequality is complete.

## Dependency map

```text
Concrete J/R machinery
  -> concrete_main_comparison
  -> direct_paper_consequence
  -> alphaQ existence and alphaQ_spec
  -> J (alphaQ+1) (L n) <= Q m n
  -> SourceRecurrence F at k = alphaQ+1
  -> ceilDiv/Q arithmetic
  -> finite source cost theorem

Threshold arithmetic
  -> integral/nonintegral sourceThreshold cases
  -> Ackermann buffer
  -> alphaJS <= alphaQ + 2

Source recurrence interface
  -> finite source cost theorem
  -> final paper wrapper
```

## Scout verdict

The remaining theorem is no longer blocked by the top-down comparison
machinery. The core remaining choice is architectural: formalize the final cost
bound through a conditional source recurrence interface now, and leave the
actual source recurrence/model formalization for a separate future project.
