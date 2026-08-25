/-
  THE NU ACT'S DECIDED CORE · ShareDependenceShadow.lean
  ======================================================

  Ferry 2026-08-25 (b155). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b154 named a freedom in b38's apportionment: one unpinned share of the residual.
  THIS ACT ASKS WHETHER THAT FREEDOM IS GAUGE — whether the identity's finite
  instance can see it at all. The answer's arithmetic skeleton is here; the census
  that gives it its content (which of the identity's four terms carry the share)
  is a READ, done in the bank, and is NOT in this module.

  THE MODEL: an identity's cleared residual at a cell, as a function of the share
  numerator `p` over denominator `q`, is `res(p) = E − p·R − C`, where `R` is the
  multiplier the share rides (the residual being apportioned) and `E`, `C` collect
  everything share-free. Rationals are cleared, so every statement is over ℤ.

  · `share_dependence_is_exactly_R` — the whole share-dependence, at instances:
    `res(p) − res(p′) = −(p − p′)·R`. Nothing else moves.
  · `gauge_iff_R_zero` — ### THE TEST ITSELF, IN BOTH POLARITIES. On the GAUGE
    instances (`R = 0`) two different shares give the IDENTICAL residual: the
    freedom is invisible and the choice is convention. On the PHYSICAL instances
    (`R ≠ 0`) they give DIFFERENT residuals: the freedom is visible and at most one
    share can be admissible. ### A test that only ever returned one verdict would
    decide nothing, which is why both families are carried and checked.
  · `at_most_one_share_zeroes_it` — on the physical instances, the designated share
    zeroes the residual and the competitor does NOT.
  · `no_single_share_serves_two_cells` — ### THE OVER-DETERMINATION: two cells whose
    required shares differ cannot both be zeroed by one share, and a share is ONE
    definitional choice serving every cell. Each instance carries BOTH negative
    witnesses (cell 1's share fails cell 2, and cell 2's fails cell 1).

  ### WITNESS DISCIPLINE, AND WHY IT IS STATED: b154's module failed its own first
  ### run because four of five "competitor" fixtures were accidentally the POSITIVE
  ### case — the negative polarity was ASSERTED, not verified. Here every instance's
  ### polarity was CHECKED BEFORE THIS FILE WAS WRITTEN, and the check is banked.

  Scope, on its face: these are the arithmetic's INSTANCES. ### NOTHING HERE SAYS
  WHICH SHARE IS RIGHT, that any share makes any identity true, or that the identity
  holds at any cell — b38's recorded (I-differ) verdict stands untouched and is
  neither re-interpreted nor extended by any line of this module. Nothing here bears
  on `h2`. Bank: relay data/b155_nu.txt.
-/

set_option maxRecDepth 16384

namespace ShareDependenceShadow

/-- the cleared identity residual at a cell, as a function of the share numerator:
    `E` and `C` collect every share-free term, `R` is the multiplier the share rides. -/
def res (E R C p : Int) : Int := E - p * R - C

/-- PHYSICAL instances: `(E, R, C, p₀, p′)` with `R ≠ 0`, `p₀` zeroing the residual
    and `p′` a competitor that does not. Polarity verified before this file existed. -/
def physCases : List (Int × Int × Int × Int × Int) :=
  [ (100, 7, 30, 10, 11),
    (-45, 3, 6, -17, -16),
    (1000, -25, 1250, 10, 0),
    (0, 1, 0, 0, 5) ]

/-- GAUGE instances: `(E, 0, C, p, p′)` — the multiplier vanishes, so the residual
    cannot see the share. Note the second is zero and the first is not: ### GAUGE
    MEANS THE RESIDUAL CANNOT SEE THE SHARE, NOT THAT IT VANISHES. -/
def gaugeCases : List (Int × Int × Int × Int × Int) :=
  [ (100, 0, 30, 10, 11),
    (7, 0, 7, 3, -4) ]

/-- PAIRS: `((E₁,R₁,C₁,p₁), (E₂,R₂,C₂,p₂))` — two cells whose required shares differ. -/
def pairCases : List ((Int × Int × Int × Int) × (Int × Int × Int × Int)) :=
  [ ((100, 7, 30, 10), (90, 5, 20, 14)),
    ((-45, 3, 6, -17), (12, 4, 0, 3)) ]

/-- THE WHOLE SHARE-DEPENDENCE, decided: two shares' residuals differ by exactly
    `−(p − p′)·R`. However elaborate the cell, the share reaches the residual
    through this one product. -/
theorem share_dependence_is_exactly_R :
    (physCases.all (fun t =>
      decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.1 - res t.1 t.2.1 t.2.2.1 t.2.2.2.2
              = - (t.2.2.2.1 - t.2.2.2.2) * t.2.1))
     && gaugeCases.all (fun t =>
      decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.1 - res t.1 t.2.1 t.2.2.1 t.2.2.2.2
              = - (t.2.2.2.1 - t.2.2.2.2) * t.2.1))) = true := by
  decide

/-- ### THE GAUGE TEST, IN BOTH POLARITIES. `R = 0` ⇒ the two shares give the SAME
    residual (the freedom is convention). `R ≠ 0` ⇒ they give DIFFERENT residuals
    (the freedom is visible, and at most one share can be admissible). -/
theorem gauge_iff_R_zero :
    (gaugeCases.all (fun t =>
      decide (t.2.1 = 0)
      && decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.1 = res t.1 t.2.1 t.2.2.1 t.2.2.2.2))
     && physCases.all (fun t =>
      !decide (t.2.1 = 0)
      && !decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.1 = res t.1 t.2.1 t.2.2.1 t.2.2.2.2))) = true := by
  decide

/-- AT MOST ONE SHARE ZEROES IT, at the physical instances: the designated share
    zeroes the residual and the competitor does not. The second conjunct is the
    NEGATIVE witness and is the half that carries the content. -/
theorem at_most_one_share_zeroes_it :
    physCases.all (fun t =>
      decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.1 = 0)
      && !decide (res t.1 t.2.1 t.2.2.1 t.2.2.2.2 = 0)) = true := by
  decide

/-- ### THE OVER-DETERMINATION, decided: two cells whose required shares differ
    cannot both be zeroed by one share — and a share is ONE definitional choice
    serving every cell, not a per-cell fit. Both negative witnesses are carried. -/
theorem no_single_share_serves_two_cells :
    pairCases.all (fun c =>
      !decide (c.1.2.2.2 = c.2.2.2.2)
      && decide (res c.1.1 c.1.2.1 c.1.2.2.1 c.1.2.2.2 = 0)
      && decide (res c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 = 0)
      && !decide (res c.2.1 c.2.2.1 c.2.2.2.1 c.1.2.2.2 = 0)
      && !decide (res c.1.1 c.1.2.1 c.1.2.2.1 c.2.2.2.2 = 0)) = true := by
  decide

end ShareDependenceShadow

#print axioms ShareDependenceShadow.share_dependence_is_exactly_R
#print axioms ShareDependenceShadow.gauge_iff_R_zero
#print axioms ShareDependenceShadow.at_most_one_share_zeroes_it
#print axioms ShareDependenceShadow.no_single_share_serves_two_cells
