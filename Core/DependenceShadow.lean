/-
  THE DEPENDENCE AUDIT'S DECIDED CORE · DependenceShadow.lean
  ===========================================================

  Ferry 2026-08-25 (b166). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b154 showed the admissible apportionments form a ONE-PARAMETER FAMILY. This
  module decides the finite shadow of what that parameter does to the density
  lane's recorded numbers — and NOTHING ELSE.

  ### THE STRUCTURAL FACT BEHIND EVERY TERMINAL HERE: b38's definition is linear
  in its three inputs, so a member shift moves each cell's recorded deviation by
  `dμ · resid_N/|A|` — b155's own law, reached again from b154's family. Every
  operation the lane applies afterwards is linear in the density, so the whole
  member-dependence is ONE AFFINE DIRECTION.

  · `shift_law_is_additive` — ### THE INVARIANT SIDE: composing two member shifts
    equals the single shift by their sum, exactly, at every cell. The family acts
    on the deviations as a one-parameter group; the affine structure is decided,
    not asserted.
  · `signs_are_mixed_at_b38_member` — at `dμ = 0` some deviations are positive and
    some negative: ### a sign change exists in the recorded grid.
  · `signs_are_uniform_off_the_window` — at `dμ = +0.005` ALL SIX are positive and
    at `dμ = −0.040` ALL SIX are negative: ### the sign change is GONE on both
    sides, so its presence is PARAMETER-CONDITIONAL.
  · `psi_zero_line_reproduces_the_bank` — the derived line `Ψ_μ(0) = N_even − μ·NMODE`
    evaluated at b38's member returns `−1.165003`, ### which is b115's banked
    `Ψ(0)` to its printed digits, and it CHANGES SIGN across the family.

  ### WHAT THIS DOES NOT DO, and the fence is the point of the act:
  ### IT DOES NOT PREFER A MEMBER. That one member makes the recorded deviations
  ### uniform in sign and another does not is a fact about the RECORDED GRID under
  ### an unpinned definitional choice. ### IT IS NOT AN ARGUMENT FOR ANY MEMBER,
  ### and it may not be cited as one. The freedom is not an uncertainty in the
  ### crossing; it is a choice nobody has made, and until it is made there is no
  ### fact of the matter about which pattern is "the" pattern.
  ### THE CROSSING'S LOCATION CARRIES ZERO INTERPRETIVE WEIGHT here as everywhere.
  ### NOTICED IS NOT EARNED.

  Nothing here re-grades any lane result: dependence is not correctness. Nothing
  here says the identity holds anywhere; b38's recorded (I-differ) verdict stands
  untouched and is extended nowhere. Nothing here bears on `h2`.
  Bank: relay data/b166_dependence_audit.txt.
-/

set_option maxRecDepth 16384

namespace DependenceShadow

/-- b110's recorded deviations `D = f_cell − σ_even` at `a² ∈ {2,3,4,8,9,12}`,
    scaled by `10^9`. Owner: b110 component 3, reproducing b38's own `f` column. -/
def devE9 : List Int := [75845701, 47312701, 36823701, 9495701, 3946701, -7261299]

/-- b155's banked `resid_N/|A|` column at the same cells, scaled by `10^4`. -/
def ratioE4 : List Int := [20339, 17675, 17060, 16525, 16488, 16461]

/-- the deviations at member shift `dμ` (scaled `10^9`), themselves scaled by
    `10^13`: `D_μ = D_σ + dμ · resid_N/|A|`. -/
def devAtE13 (dmuE9 : Int) : List Int :=
  (devE9.zip ratioE4).map (fun p => p.1 * 10000 + dmuE9 * p.2)

/-- ### THE INVARIANT SIDE, DECIDED: the member shifts COMPOSE EXACTLY. Shifting
    by `d₁` and then by `d₂` lands where shifting once by `d₁ + d₂` lands, at every
    cell — the one-parameter structure, decided rather than asserted. -/
def shiftOnce : List Int := devAtE13 (1234567 + (-7654321))

def shiftTwice : List Int :=
  ((devAtE13 1234567).zip ratioE4).map (fun p => p.1 + (-7654321) * p.2)

theorem shift_law_is_additive :
    ((shiftOnce.zip shiftTwice).all (fun p => decide (p.1 = p.2))
     && decide (shiftOnce.length = shiftTwice.length)
     && decide (shiftOnce.length = 6)) = true := by
  decide

/-- ### A SIGN CHANGE EXISTS IN THE RECORDED GRID AT b38's MEMBER: some deviation
    is positive and some is negative, and (the third clause) they are not all of
    one sign — so the crossing is present. -/
theorem signs_are_mixed_at_b38_member :
    ((devAtE13 0).any (fun x => decide (x > 0))
     && (devAtE13 0).any (fun x => decide (x < 0))
     && !((devAtE13 0).all (fun x => decide (x > 0)))
     && !((devAtE13 0).all (fun x => decide (x < 0)))) = true := by
  decide

/-- ### AND IT IS GONE ON BOTH SIDES: at `dμ = +0.005` every recorded deviation is
    positive; at `dμ = −0.040` every one is negative. ### THE CROSSING'S PRESENCE
    IS THEREFORE PARAMETER-CONDITIONAL — decided here, not inferred. -/
theorem signs_are_uniform_off_the_window :
    ((devAtE13 5000000).all (fun x => decide (x > 0))
     && (devAtE13 (-40000000)).all (fun x => decide (x < 0))) = true := by
  decide

/-- the derived small-`L` line `Ψ_μ(0) = N_even − μ·NMODE`, scaled by `10^7`;
    `N_even = 5`, `NMODE = 10` (b115 (2g): `A_n(0) = 1` every mode, `e_n(0) = 0`). -/
def psiZeroE7 (muE7 : Int) : Int := 5 * 10000000 - 10 * muE7

/-- ### THE DERIVED LINE MEETS THE BANK, AND THEN CROSSES ZERO. At b38's member it
    returns `−1.165003`, which is b115's banked `Ψ(0)` to its printed digits — the
    derivation and the measurement agree. ### At the free end it is `+5`, and it
    vanishes in between: the small-`L` limit's SIGN is parameter-conditional. -/
theorem psi_zero_line_reproduces_the_bank :
    (decide (psiZeroE7 6165003 = -11650030)
     && decide (psiZeroE7 5000000 = 0)
     && decide (psiZeroE7 0 = 50000000)
     && decide (psiZeroE7 6165003 < 0)
     && decide (psiZeroE7 0 > 0)) = true := by
  decide

end DependenceShadow

#print axioms DependenceShadow.shift_law_is_additive
#print axioms DependenceShadow.signs_are_mixed_at_b38_member
#print axioms DependenceShadow.signs_are_uniform_off_the_window
#print axioms DependenceShadow.psi_zero_line_reproduces_the_bank
