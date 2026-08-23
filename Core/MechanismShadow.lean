/-
  THE MECHANISM ACT'S DECIDED CORE · MechanismShadow.lean
  ========================================================

  Ferry 2026-08-23 (b115). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  The act's central derived step is a COLLAPSE TO ONE DENSITY. In the analytic
  setting: the sector deviation N(a) = W₊ − σ_even·A is, by b109's identity and
  b38's own integral forms, a single integral of the window's autocorrelation
  against ONE density Ψ that carries no window parameter. The step that makes
  this work is not analysis at all — it is a finite bilinear rearrangement:
  the mode sums and the quadrature sum commute, and the sector weights are
  scalars. THAT rearrangement is what this module decides.

  Rationals are cleared: σ_even = p/q is carried as the integer pair (q, p), so
  every statement below is over ℤ and decidable.

  · `collapse_to_one_density` — THE ACT'S STEP, at decided instances: the sector
    numerator, formed as (even-mode sum minus share times total) for BOTH the
    trace matrix and the ε matrix, equals the quadrature weights dotted against
    a SINGLE density list built from the two matrices alone.
  · `one_density_two_windows` — the density carries no window: the SAME density
    list serves two different weight vectors, each reproducing its own numerator.
    This is the finite shadow of "Ψ takes no a parameter".
  · `sector_numerators_cancel` — the void gate from the other side, decided: with
    the even share p/q and the odd share (q−p)/q, the two sector numerators sum
    to exactly zero, for every instance. b109's 0 = 0 note as arithmetic.

  Scope, on its face: these are the finite rearrangement's INSTANCES. The general
  statement is written longhand in the bank; nothing here is claimed beyond the
  decided cases, and nothing here bears on the act's NAMED OPEN STEP (the sign of
  a mean-zero scale-average), which is analysis and is not touched.
  Bank: relay data/b115_mechanism.txt.
-/

set_option maxRecDepth 16384

namespace MechanismShadow

abbrev Vec : Type := List Int
abbrev Mat : Type := List Vec

/-- entrywise sum of two vectors; the longer tail survives -/
def addV : Vec → Vec → Vec
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addV xs ys

/-- entrywise difference -/
def subV : Vec → Vec → Vec
  | [], ys => ys.map (fun y => -y)
  | xs, [] => xs
  | x :: xs, y :: ys => (x - y) :: subV xs ys

/-- scalar multiple -/
def scaleV (k : Int) : Vec → Vec
  | [] => []
  | x :: xs => (k * x) :: scaleV k xs

/-- the quadrature pairing -/
def dotV : Vec → Vec → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotV xs ys

/-- entrywise sum over the rows of a matrix (the mode sum) -/
def colSum : Mat → Vec
  | [] => []
  | r :: rs => addV r (colSum rs)

/-- rows whose index has the given parity; `true` keeps the head. -/
def pickParity : Bool → Mat → Mat
  | _,     []      => []
  | true,  r :: rs => r :: pickParity false rs
  | false, _ :: rs => pickParity true rs

/-- rows at indices 0, 2, 4, … — the even sector -/
def evensOf (m : Mat) : Mat := pickParity true m
/-- rows at indices 1, 3, 5, … — the odd sector -/
def oddsOf (m : Mat) : Mat := pickParity false m

/-- the cleared sector numerator: q·(sector mode sum) − p·(total mode sum),
    formed for the trace matrix and the ε matrix and differenced, then paired
    with the window's weights. -/
def numer (q p : Int) (A E : Mat) (c : Vec) : Int :=
  (q * dotV c (colSum (evensOf A)) - p * dotV c (colSum A))
  - (q * dotV c (colSum (evensOf E)) - p * dotV c (colSum E))

/-- the same, for the ODD sector, with the odd share (q−p)/q -/
def numerOdd (q p : Int) (A E : Mat) (c : Vec) : Int :=
  (q * dotV c (colSum (oddsOf A)) - (q - p) * dotV c (colSum A))
  - (q * dotV c (colSum (oddsOf E)) - (q - p) * dotV c (colSum E))

/-- THE DENSITY: built from the two matrices and the cleared share alone.
    No window, no weights. -/
def density (q p : Int) (A E : Mat) : Vec :=
  subV (subV (scaleV q (colSum (evensOf A))) (scaleV p (colSum A)))
       (subV (scaleV q (colSum (evensOf E))) (scaleV p (colSum E)))

/-- the decided instances: (q, p, A, E, c, c′) -/
def cases : List (Int × Int × Mat × Mat × Vec × Vec) :=
  [ (4, 3, [[1, 2, 3], [0, -1, 2], [5, 1, -2], [2, 2, 2]],
           [[0, 1, -1], [3, 0, 1], [-2, 4, 0], [1, -3, 2]],
           [7, -2, 5], [1, 1, 1]),
    (10, 6, [[2, -3], [4, 1], [-1, 0], [6, 6], [0, 5], [3, -4]],
            [[1, 1], [0, 2], [7, -1], [-5, 3], [2, 2], [1, 0]],
            [3, 8], [-4, 9]),
    (1000, 617, [[1, 0, 0, 2], [0, 3, 1, -1], [4, -2, 5, 0]],
                [[2, 2, -3, 1], [1, 1, 1, 1], [0, -4, 2, 6]],
                [11, -6, 4, 13], [2, 0, -7, 1]),
    (3, 1, [[9]], [[4]], [12], [-5]),
    (7, 7, [[1, -1, 1], [2, 0, -2]], [[0, 0, 0], [3, 3, 3]], [1, 2, 3], [0, 1, 0]) ]

/-- THE COLLAPSE TO ONE DENSITY, decided at every instance: the sector numerator
    equals the window's weights paired with a single density that was built
    without them. The mode sums and the quadrature sum commute; the shares are
    scalars; nothing else is used. -/
theorem collapse_to_one_density :
    cases.all (fun t =>
      decide (numer t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
                = dotV t.2.2.2.2.1 (density t.1 t.2.1 t.2.2.1 t.2.2.2.1))) = true := by
  decide

/-- ONE DENSITY, TWO WINDOWS: the same density list reproduces the numerator for
    two different weight vectors. The finite shadow of "the density carries no
    window parameter". -/
theorem one_density_two_windows :
    cases.all (fun t =>
      decide (numer t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
                = dotV t.2.2.2.2.1 (density t.1 t.2.1 t.2.2.1 t.2.2.2.1)
              ∧ numer t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.2
                = dotV t.2.2.2.2.2 (density t.1 t.2.1 t.2.2.1 t.2.2.2.1))) = true := by
  decide

/-- THE VOID GATE FROM THE OTHER SIDE, decided: the even-sector numerator and the
    odd-sector numerator sum to exactly zero at every instance — the shares are
    complementary, so the totals cancel. b109's 0 = 0 consistency note as
    arithmetic on finite data. -/
theorem sector_numerators_cancel :
    cases.all (fun t =>
      decide (numer t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
              + numerOdd t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 = 0)) = true := by
  decide

end MechanismShadow
