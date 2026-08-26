/-
  THE RE-DERIVATION'S DECIDED CORE · ReDerivationShadow.lean
  ==========================================================

  Ferry 2026-08-26 (b176). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected profile
  per terminal: "does not depend on any axioms".

  The corpus re-derived the `(Qε)` series because the source's statement and proof were
  *"not on disk"*. ### **The source is now in hand and was read at the PDF**, and its
  Proposition 5.3 gives, with `D_u(f)(x) := x·f'(x)`:

      C_n = ρ^(1/2) ∫ (D_u ξ)(x)(D_u ξ)(ρx) dx
          + ρ^(−1/2) (D_u ξ)(ρ⁻¹) ξ(1)
          − ρ^(1/2)  ξ(1) (D_u ξ)(ρ)

  while the corpus's own `qeps_layer` implements

      C_n = ρ^(1/2) ∫ [x ξ'(x)][ρx ξ'(ρx)] dx
          + ρ^(−3/2) ξ'(ρ⁻¹) ξ(1)
          − ρ^(3/2)  ξ(1) ξ'(ρ)

  ### **THE TWO AGREE, AND WHAT MAKES THEM AGREE IS `D_u`'s ARGUMENT FACTOR** — evaluated at
  `ρ⁻¹` it contributes `ρ⁻¹`, at `ρ` it contributes `ρ`. This module decides that arithmetic,
  in HALF-INTEGER units so every quantity is an integer.

  · `expanding_the_scaling_operator_reconciles_all_three_terms` — the source's exponents,
    once `D_u` is expanded, are exactly the corpus's, term for term.
  · `the_unexpanded_form_does_not_match` — ### **and without that expansion they do NOT
    match**, so the agreement is a fact about `D_u` and not a coincidence of notation.

  ### **WHAT THIS DOES NOT DO:** it does not verify either formula against the mathematics
  they describe, and it is ### **not evidence for the identity, for `h2`, for the
  apportionment, or for any member.** ***It decides that a re-derivation and its source
  write the same thing.*** The re-derivation stands at its own grade, undisturbed.
  ### **AND THE POINTERS DIVERGE WHERE THE MATHEMATICS DOES NOT:** the corpus cites this as
  *"their Prop 5.3 / eq (100)"* and the PDF carries it at **(98)** — a VERSION difference,
  ### **which the corpus's own header anticipated by naming its numbering source.**

  Bank: relay data/b176_seam_and_reads.txt.
-/

set_option maxRecDepth 16384

namespace ReDerivationShadow

/-- exponents of `ρ` in HALF-INTEGER units, so all arithmetic is integer.
    The source's stated prefactors: `ρ^(1/2)`, `ρ^(−1/2)`, `ρ^(1/2)`. -/
def sourcePrefactors : List Int := [1, -1, 1]

/-- `D_u(f)(x) = x·f'(x)` contributes its ARGUMENT as a factor: nothing in the integral term
    (where it is written out), `ρ⁻¹` in the second, `ρ` in the third. -/
def scalingOperatorFactors : List Int := [0, -2, 2]

/-- what the corpus's `qeps_layer` implements: `ρ^(1/2)`, `ρ^(−3/2)`, `ρ^(3/2)`. -/
def corpusExponents : List Int := [1, -3, 3]

/-- the source's exponents once `D_u` is expanded. -/
def sourceExpanded : List Int :=
  (sourcePrefactors.zip scalingOperatorFactors).map (fun p => p.1 + p.2)

/-- ### THE RE-DERIVATION AND ITS SOURCE WRITE THE SAME THING, decided term for term: with
    `D_u` expanded, the source's three exponents are exactly the corpus's, and the lists have
    the same length so no term is dropped by a truncating zip. -/
theorem expanding_the_scaling_operator_reconciles_all_three_terms :
    ((sourceExpanded.zip corpusExponents).all (fun p => decide (p.1 = p.2))
     && decide (sourceExpanded.length = 3)
     && decide (corpusExponents.length = 3)) = true := by
  decide

/-- ### AND WITHOUT THE EXPANSION THEY DO NOT MATCH — so the agreement is a fact about `D_u`'s
    argument factor and not a coincidence of notation. Decided at both terms that move. -/
theorem the_unexpanded_form_does_not_match :
    (!((sourcePrefactors.zip corpusExponents).all (fun p => decide (p.1 = p.2)))
     && decide ((sourcePrefactors.drop 1).head? ≠ (corpusExponents.drop 1).head?)
     && decide ((sourcePrefactors.drop 2).head? ≠ (corpusExponents.drop 2).head?)
     && decide (sourcePrefactors.head? = corpusExponents.head?)) = true := by
  decide

end ReDerivationShadow

#print axioms ReDerivationShadow.expanding_the_scaling_operator_reconciles_all_three_terms
#print axioms ReDerivationShadow.the_unexpanded_form_does_not_match
