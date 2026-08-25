/-
  THE FAMILY SIGN WINDOW'S DECIDED CORE · FamilySignShadow.lean
  =============================================================

  Ferry 2026-08-25 (b168). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b166 derived that the density lane's whole member-dependence is ONE AFFINE
  DIRECTION: `I_μ(L) = I_σ(L) + (σ_even − μ)·J(L)`. b167 halted because `Δ`, which
  generates that direction, could not be measured — the ε grid's first node sat at
  `exp(1e-4)` and `np.interp` clamped below it. b168 repaired the grid's DOMAIN and
  measured `J`.

  This module decides the finite shadow of what the measurement returned, at the
  nine recorded cells, and NOTHING else. Writing `d := σ_even − μ`, each cell
  contributes `I_σ + d·J`, in integers scaled by `10^21`.

  · `pairings_all_negative_and_slopes_all_positive` — at b38's member every one of
    the nine pairings is negative, and ### every `J` is POSITIVE. The second half is
    what makes the admissible set a HALF-LINE rather than an interval: with no sign
    change in `J`, the constraint binds from one side only.
  · `binding_cell_is_the_smallest` — `a² = 2` minimises `−I/J` across the nine, by
    cross-multiplication, so it is the cell that fixes the threshold.
  · `holds_at_b38_member_and_at_one_fails_at_zero` — all nine negative at
    `μ = σ_even` and at `μ = 1`; ### at `μ = 0` at least one is POSITIVE.
  · `threshold_brackets_the_endpoint` — `d = 0.132` keeps all nine negative and
    `d = 0.133` does not, so the endpoint is bracketed between them.

  ### WHAT THIS DOES NOT DO, AND THE FENCE IS THE POINT OF THE ACT:
  ### IT DOES NOT ARGUE FOR OR AGAINST ANY MEMBER. That the one-sign property fails
  ### at `μ = 0` is NOT evidence against `μ = 0`. The inference "this member breaks
  ### the lane, so this member is wrong" needs a premise nobody has — that the
  ### lane's monotonicity is a REQUIREMENT. It never was: b115, b116 and b117 were
  ### finding out WHETHER it holds, not assuming it must. A member that does not
  ### preserve it simply leaves the balanced window's uniqueness underived.
  ### THE SUBRANGE IS A FACT ABOUT THE FAMILY AND NEVER AN ARGUMENT FOR A MEMBER.
  ### NOTICED IS NOT EARNED.

  The inputs are BENCH values carrying their instrument's grade and its stated
  conditionality; deciding them here does not upgrade them. Nothing here re-grades
  any lane result, says the identity holds anywhere, or bears on `h2`; b38's
  recorded (I-differ) verdict stands untouched.
  Bank: relay data/b168_left_endpoint.txt.
-/

set_option maxRecDepth 16384

namespace FamilySignShadow

/-- `I_σ(L)` at `a² ∈ {2,3,4,8,9,12,16,24,48}`, scaled by `10^12`. -/
def IsigE12 : List Int :=
  [-141878140014, -101477079811, -94958249834, -96080945837, -96586799482,
   -97074298101, -96237114469, -92834734594, -82552767163]

/-- `J(L)` at the same cells, scaled by `10^12`. Measured on the repaired grid. -/
def JE12 : List Int :=
  [1068344313137, 677840421280, 540571529946, 371318540385, 353989310753,
   319441864457, 293121139854, 265584214351, 234599094014]

/-- `I_μ = I_σ + d·J` at every cell, with `d := σ_even − μ` scaled by `10^9`;
    the result is scaled by `10^21`. -/
def pairingsE21 (dE9 : Int) : List Int :=
  (IsigE12.zip JE12).map (fun p => p.1 * 1000000000 + dE9 * p.2)

/-- ### AT b38's MEMBER EVERY PAIRING IS NEGATIVE, AND EVERY SLOPE IS POSITIVE.
    The second clause is the structural one: `J` has no sign change across the nine,
    so the admissible set is a HALF-LINE, not a two-sided interval. -/
theorem pairings_all_negative_and_slopes_all_positive :
    ((pairingsE21 0).all (fun x => decide (x < 0))
     && JE12.all (fun j => decide (j > 0))
     && decide (IsigE12.length = 9)
     && decide (JE12.length = 9)) = true := by
  decide

/-- ### `a² = 2` IS THE BINDING CELL: it minimises `−I/J` across the nine, decided by
    cross-multiplication so no division is needed and no rounding enters. -/
theorem binding_cell_is_the_smallest :
    ((IsigE12.zip JE12).all (fun p =>
        decide ((-(-141878140014 : Int)) * p.2 ≤ (-p.1) * 1068344313137))) = true := by
  decide

/-- ### THE VERDICT'S THREE NAMED MEMBERS, DECIDED. All nine pairings negative at
    `μ = σ_even` (`d = 0`) and at `μ = 1` (`d = −0.383499701`); ### at `μ = 0`
    (`d = +0.616500299`) at least one is POSITIVE, so the one-sign property does not
    hold there. -/
theorem holds_at_b38_member_and_at_one_fails_at_zero :
    ((pairingsE21 0).all (fun x => decide (x < 0))
     && (pairingsE21 (-383499701)).all (fun x => decide (x < 0))
     && (pairingsE21 616500299).any (fun x => decide (x > 0))
     && !((pairingsE21 616500299).all (fun x => decide (x < 0)))) = true := by
  decide

/-- ### THE ENDPOINT IS BRACKETED: `d = 0.132` keeps all nine negative and
    `d = 0.133` does not. Decided at both ends, so neither side is assumed. -/
theorem threshold_brackets_the_endpoint :
    ((pairingsE21 132000000).all (fun x => decide (x < 0))
     && !((pairingsE21 133000000).all (fun x => decide (x < 0)))) = true := by
  decide

end FamilySignShadow

#print axioms FamilySignShadow.pairings_all_negative_and_slopes_all_positive
#print axioms FamilySignShadow.binding_cell_is_the_smallest
#print axioms FamilySignShadow.holds_at_b38_member_and_at_one_fails_at_zero
#print axioms FamilySignShadow.threshold_brackets_the_endpoint
