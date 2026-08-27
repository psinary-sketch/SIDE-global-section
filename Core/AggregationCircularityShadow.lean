/-
  THE AGGREGATION'S FREEDOM, AND WHY C-WEIL CANNOT NARROW IT
  · AggregationCircularityShadow.lean
  ==========================================================

  Ferry 2026-08-27 (b220, the aggregation's freedom). Vanilla Lean 4
  (v4.29.1 pinned), no imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF — AND WHAT IT IS **NOT**.
  b215 found term 2's missing sentence: how the quotient channel's per-place,
  per-level values become the single real `Q.value` at a diagonal cell.
  b220 enumerates the constraints the record imposes on that sentence.

  ### **THIS FILE DEFINES NO AGGREGATION.** `agg` is a variable throughout and
  nothing here is written into File E. The scope line of b220's ferry governs:
  *"any aggregation written would compile, so none is written into File E."*
  ### **NO AGGREGATION IS ADOPTED, DEFINED, OR COMPILED.**

  ### WHAT IT DOES SHADOW: **THE CIRCULARITY**.
  One candidate constraint — call it C-WEIL — is *"the aggregate reproduces
  Weil's coefficients"*, i.e. the aggregation is required to satisfy File E's
  identity `T.value + Q.value = W.wInf - W.wPrimes`.
  ### **That identity's truth at complete roster is `h2`.** File E's own
  docstring says it is *"STATED, NOT PROVED, NOT CLAIMED"*, and act 7 says of
  exactly this comparison: ### *"Its coefficients against Weil's: part of
  (L-identity), NOT ASSUMED."*

  This file makes the consequence checkable rather than merely stated:

    (1) the identity determines the quotient value UNIQUELY (`unique`);
    (2) an aggregation satisfies C-WEIL IFF it returns that forced value at
        every cell (`cweil_determines`) — so C-WEIL does not *narrow* a family,
        ### **it PRESCRIBES the single member that makes the identity true**;
    (3) that aggregation EXISTS (`cweil_inhabited`) — so C-WEIL is satisfiable
        and its satisfaction is therefore no evidence about `h2`;
    (4) ### **the punchline** (`cweil_is_the_assumption`): the proof that the
        identity holds for such an aggregation IS the C-WEIL hypothesis itself,
        returned unchanged. Not an argument — the assumption in other clothes;
    (5) by contrast C-TYPE admits more than one aggregation
        (`underdetermined_without_cweil`) — the freedom is not a point.

  ### THE ABSTRACTION, AND WHY IT IS THE HONEST ONE. Core is import-free, so
  there is no `ℝ` here. Rather than substitute `Int` silently, the file states
  the EXACT structure the argument uses — ### **additive cancellation, and
  nothing else**: no ordering, no completeness, no field property, no
  multiplication. ### **`ℝ` has this structure, so the argument transfers; the
  shadow is weaker than File E in its objects and EXACTLY AS STRONG in its
  reasoning.**

  ### AND THE STRUCTURE IS **INHABITED**, WHICH IS NOT DECORATION.
  b215's own shell test convicts a structure that nothing satisfies. `boolGrp`
  exhibits `Bool` under XOR — `Z/2`, a genuine group with two distinct
  elements — so no theorem below is vacuously about an empty class, and
  `underdetermined_bool` instantiates the contrast rather than stating it.
  ### **A shadow whose hypotheses nothing satisfies is a shell, and this act
  refuses to file one.**
-/

namespace AggregationCircularityShadow

/-- the exact structure the circularity argument needs: an additive group,
    given by its laws as fields. ### NO ORDER, NO MULTIPLICATION, NO
    COMPLETENESS — the argument uses cancellation and nothing more. -/
structure Grp (α : Type) where
  add : α → α → α
  neg : α → α
  zero : α
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  neg_add : ∀ a, add (neg a) a = zero
  add_neg : ∀ a, add a (neg a) = zero

variable {α : Type} (G : Grp α)

/-- File E's finite-instance identity at one cell: `t` the archimedean trace,
    `q` the quotient trace, `x` the ledger's `wInf - wPrimes`.
    ### STATED, NEVER ASSERTED. -/
def identity (t q x : α) : Prop := G.add t q = x

/-- the quotient value the identity forces, read straight off it. -/
def forced (t x : α) : α := G.add (G.neg t) x

theorem identity_iff_forced (t q x : α) :
    identity G t q x ↔ q = forced G t x := by
  apply Iff.intro
  · intro h
    have s0 : G.add (G.neg t) x = G.add (G.neg t) (G.add t q) :=
      congrArg (fun z => G.add (G.neg t) z) h.symm
    have s1 : G.add (G.neg t) (G.add t q) = G.add (G.add (G.neg t) t) q :=
      (G.add_assoc (G.neg t) t q).symm
    have s2 : G.add (G.add (G.neg t) t) q = G.add G.zero q :=
      congrArg (fun z => G.add z q) (G.neg_add t)
    exact (s0.trans (s1.trans (s2.trans (G.zero_add q)))).symm
  · intro h
    have s0 : G.add t q = G.add t (G.add (G.neg t) x) :=
      congrArg (fun z => G.add t z) h
    have s1 : G.add t (G.add (G.neg t) x) = G.add (G.add t (G.neg t)) x :=
      (G.add_assoc t (G.neg t) x).symm
    have s2 : G.add (G.add t (G.neg t)) x = G.add G.zero x :=
      congrArg (fun z => G.add z x) (G.add_neg t)
    exact s0.trans (s1.trans (s2.trans (G.zero_add x)))

/-- (1) ### THE IDENTITY DETERMINES THE QUOTIENT VALUE UNIQUELY. -/
theorem unique (t q1 q2 x : α)
    (h1 : identity G t q1 x) (h2 : identity G t q2 x) : q1 = q2 :=
  ((identity_iff_forced G t q1 x).mp h1).trans
    ((identity_iff_forced G t q2 x).mp h2).symm

/-- an aggregation is any assignment of one value to each cell. ### THIS IS
    ALL C-TYPE DEMANDS: File E's `QuotientTrace` carries `value : ℝ` and
    nothing else — no linearity, no per-place factorization, no positivity. -/
def Aggregation (Cell : Type) (α : Type) := Cell → α

/-- C-WEIL as a constraint on an aggregation: it satisfies the identity at
    every cell. -/
def SatisfiesCWeil {Cell : Type} (agg : Aggregation Cell α)
    (t : Cell → α) (x : Cell → α) : Prop :=
  ∀ c, identity G (t c) (agg c) (x c)

/-- (2) ### **THE CIRCULARITY.** An aggregation satisfies C-WEIL exactly when
    it returns the forced value at every cell. ### C-WEIL does not narrow a
    family of candidates; ### **IT NAMES ONE MEMBER, BY SOLVING THE IDENTITY
    FOR IT.** -/
theorem cweil_determines {Cell : Type} (t x : Cell → α)
    (agg : Aggregation Cell α) :
    SatisfiesCWeil G agg t x ↔ ∀ c, agg c = forced G (t c) (x c) :=
  Iff.intro
    (fun h c => (identity_iff_forced G (t c) (agg c) (x c)).mp (h c))
    (fun h c => (identity_iff_forced G (t c) (agg c) (x c)).mpr (h c))

/-- (3) ### AND IT IS INHABITED — C-WEIL is satisfiable for ANY `t` and ANY
    ledger. ### So "an aggregation satisfying C-WEIL exists" says nothing
    whatever about `h2`: it is true by construction. -/
theorem cweil_inhabited {Cell : Type} (t x : Cell → α) :
    SatisfiesCWeil G (fun c => forced G (t c) (x c)) t x :=
  fun c => (identity_iff_forced G (t c) (forced G (t c) (x c)) (x c)).mpr rfl

/-- (4) ### **THE PUNCHLINE, AND ITS PROOF IS THE POINT.** If an aggregation
    is chosen to satisfy C-WEIL, the identity holds at every cell — and the
    proof is the hypothesis itself, returned unchanged.
    ### **A CONSTRAINT THAT IS THE CONCLUSION PROVES THE CONCLUSION BY
    RETURNING IT.** -/
theorem cweil_is_the_assumption {Cell : Type} (t x : Cell → α)
    (agg : Aggregation Cell α) (h : SatisfiesCWeil G agg t x) :
    ∀ c, identity G (t c) (agg c) (x c) := h

/-- (5) ### THE CONTRAST. With C-WEIL unavailable, C-TYPE alone leaves more
    than one aggregation, so the freedom is not a point. -/
theorem underdetermined_without_cweil {Cell : Type} (c0 : Cell)
    (u v : α) (huv : u ≠ v) :
    ∃ a b : Aggregation Cell α, a ≠ b :=
  ⟨fun _ => u, fun _ => v, fun h => huv (congrFun h c0)⟩

/-- ### THE INHABITANT, SO NOTHING ABOVE IS VACUOUS: `Bool` under XOR, which
    is `Z/2`. ### **A GENUINE GROUP WITH TWO DISTINCT ELEMENTS**, so it also
    witnesses `underdetermined_without_cweil` rather than satisfying it
    trivially.
    ### WHY NOT `Int`. `Int` is the closer stand-in for `ℝ` and it WAS built
    and compiled first — ### **but core Lean's own `Int.add_assoc` carries
    `[propext]`, and `Core`'s print is 366 lines with ZERO axiom-bearing
    entries.** ### **This act declines to be the first to break that bar for
    a convenience instance.** *The theorems above are general over any `Grp`,
    and `ℝ` is one — that transfer is a fact about `ℝ`, not a Lean artifact,
    and it is stated in prose rather than smuggled in as an axiom.* -/
def boolGrp : Grp Bool where
  add := Bool.xor
  neg := fun b => b
  zero := false
  add_assoc := by decide
  zero_add := by decide
  neg_add := by decide
  add_neg := by decide

theorem boolGrp_has_two_elements : (false : Bool) ≠ true := by decide

/-- ### the contrast, INSTANTIATED rather than merely stated: at a nonempty
    cell type there really are two different aggregations into `Bool`. -/
theorem underdetermined_bool {Cell : Type} (c0 : Cell) :
    ∃ a b : Aggregation Cell Bool, a ≠ b :=
  underdetermined_without_cweil c0 false true boolGrp_has_two_elements

end AggregationCircularityShadow

#print axioms AggregationCircularityShadow.identity_iff_forced
#print axioms AggregationCircularityShadow.unique
#print axioms AggregationCircularityShadow.cweil_determines
#print axioms AggregationCircularityShadow.cweil_inhabited
#print axioms AggregationCircularityShadow.cweil_is_the_assumption
#print axioms AggregationCircularityShadow.underdetermined_without_cweil
#print axioms AggregationCircularityShadow.boolGrp
#print axioms AggregationCircularityShadow.boolGrp_has_two_elements
#print axioms AggregationCircularityShadow.underdetermined_bool
