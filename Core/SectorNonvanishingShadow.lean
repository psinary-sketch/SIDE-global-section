/-
  THE SECTOR DIMENSION LAWS' NONVANISHING, ALL LEVELS · SectorNonvanishingShadow.lean
  ===================================================================================

  Ferry 2026-08-26 (b198, the nonvanishing question). Vanilla Lean 4 (v4.29.1
  pinned), no imports; expected profile per terminal: "does not depend on any
  axioms" — AND THE PROFILE IS PRINTED, NEVER ASSUMED.

  THE LAWS ENTER AS BANKED DATA, NOT AS CLAIMS OF THIS FILE. Correspondence
  row 36 (b57) records them as "THEOREMS of the sector arithmetic at every
  level", derived longhand general in its registration, integer endpoints
  decided at eight banked cells:

      odd q    :  4·d₁ = (q−1)²     shape (d, d, d, d)
      place 2  :  4·d₁ = q(q−2)     shape (d, d, d+1, d)

  ### THIS FILE DOES NOT RE-DERIVE ROW 36's LONGHAND AND DOES NOT CLAIM IT.
  Each theorem below takes the law AS A HYPOTHESIS and draws the one inference
  it is entitled to draw: ### THE LAW'S RIGHT-HAND SIDE IS POSITIVE AT EVERY
  LEVEL, SO d₁ IS POSITIVE AT EVERY LEVEL. What is new here is the RANGE: row
  36's endpoints are decided at eight cells; these are general in the parameter.

  ### NOTHING BELOW REACHES THE ARCHIMEDEAN PLACE. These are finite-place laws,
  and ℝ has no finite exact levels (`LocalLimit.real_no_compact_open_addSubgroup`,
  PROVED) — so ∞ has no q, no level, and no instance of any statement here.

  THE PARAMETRIZATIONS, CHOSEN TO AVOID Nat SUBTRACTION ENTIRELY:
  · odd q ≥ 3 is written q = 2m+3, so q−1 = 2m+2  (m : Nat, unrestricted);
  · q = 2ⁿ with n ≥ 2 is written q = 4t+4, so q−2 = 4t+2  (t : Nat, unrestricted);
  · q = 2 — the arrival depth, n = 1 — is OUTSIDE the second parametrization,
    ### which is the content and not an omission: it is the one cell where the
    ### law gives ZERO, and it is decided first, below.

  Bank: relay `data/b198_nonvanishing.txt`. Gate: `data/audit_b198_gate.txt`
  (row 36's two laws against all eight banked cells, the zero cell among them).
-/

namespace SectorNonvanishingShadow

/-! ### THE POLARITY CONTROL, FIRST — THE LAW'S OWN ZERO CELL.

  A positivity theorem proved beside a law that could not produce its own zero
  would be a theorem about nothing. ### So the zero is decided BEFORE any
  positivity is stated. -/

/-- the place-2 law's right-hand side at the arrival depth `q = 2`:
    `q(q−2) = 2·0 = 0`. Decided. -/
theorem arrival_rhs_zero : 2 * 0 = 0 := by decide

/-- THE ARRIVAL-DEPTH DEATH, from the law: if `4·d₁ = q(q−2)` at `q = 2`, then
    `d₁ = 0`. ### The death at `(2,1)` is the law's OWN value. -/
theorem arrival_dim_zero : (d : Nat) → 4 * d = 2 * 0 → d = 0
  | 0,     _ => rfl
  | k + 1, h =>
    absurd (h ▸ Nat.mul_pos (by decide : 0 < 4) (Nat.succ_pos k)) (by decide)

/-- and the banked tuple's shape at that cell — `(0, 0, 1, 0)` summing to
    `dim Son(2,1) = 1` under `(d, d, d+1, d)`. Decided. -/
theorem arrival_shape : 0 + 0 + (0 + 1) + 0 = 1 := by decide

/-! ### THE EIGHT BANKED CELLS, RE-DECIDED FROM THE LAWS THEMSELVES — the gate,
  in the kernel. Each conjunct is the law's own equation at that cell, not a
  lookup of a stored number. -/

/-- the place-2 law `4·d₁ = q(q−2)` at `q = 2, 4, 8, 16` — `d₁ = 0, 2, 12, 56`. -/
theorem banked_place2_cells :
    (4 * 0 = 2 * 0) ∧ (4 * 2 = 4 * 2) ∧ (4 * 12 = 8 * 6) ∧ (4 * 56 = 16 * 14) := by
  decide

/-- the odd law `4·d₁ = (q−1)²` at `q = 3, 5, 9, 27` — `d₁ = 1, 4, 16, 169`. -/
theorem banked_odd_cells :
    (4 * 1 = 2 * 2) ∧ (4 * 4 = 4 * 4) ∧ (4 * 16 = 8 * 8) ∧ (4 * 169 = 26 * 26) := by
  decide

/-! ### THE BRIDGE, AND THE TWO POSITIVITIES. -/

/-- from `4·d > 0` to `d > 0` — the one step between the law's shape and the
    sector's dimension. -/
theorem pos_of_four_mul_pos : (d : Nat) → 0 < 4 * d → 0 < d
  | 0,     h => absurd h (by decide)
  | _ + 1, _ => Nat.succ_pos _

/-- the ODD law's right-hand side `(q−1)² = (2m+2)²` is positive for every `m`. -/
theorem odd_rhs_pos (m : Nat) : 0 < (2 * m + 2) * (2 * m + 2) :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

/-- the PLACE-2 law's right-hand side `q(q−2) = (4t+4)(4t+2)` is positive for
    every `t` — i.e. at every level beyond the arrival depth. -/
theorem place2_rhs_pos (t : Nat) : 0 < (4 * t + 4) * (4 * t + 2) :=
  Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)

/-! ### THE TWO NONVANISHING STATEMENTS, GENERAL IN THE LEVEL. -/

/-- ### THE ODD-PLACE SECTOR IS NONZERO AT EVERY LEVEL. Given the banked law
    `4·d₁ = (q−1)²` at any odd `q = 2m+3` — hence at `q = pⁿ` for every odd
    prime `p` and every level `n ≥ 1` — the sector dimension is positive. -/
theorem odd_sector_pos (m d : Nat) (hlaw : 4 * d = (2 * m + 2) * (2 * m + 2)) :
    0 < d :=
  pos_of_four_mul_pos d (hlaw ▸ odd_rhs_pos m)

/-- ### THE PLACE-2 SECTOR IS NONZERO AT EVERY LEVEL BEYOND THE ARRIVAL DEPTH.
    Given the banked law `4·d₁ = q(q−2)` at any `q = 4t+4` — hence at `q = 2ⁿ`
    for every `n ≥ 2` — the sector dimension is positive. -/
theorem place2_sector_pos (t d : Nat) (hlaw : 4 * d = (4 * t + 4) * (4 * t + 2)) :
    0 < d :=
  pos_of_four_mul_pos d (hlaw ▸ place2_rhs_pos t)

end SectorNonvanishingShadow

#print axioms SectorNonvanishingShadow.arrival_rhs_zero
#print axioms SectorNonvanishingShadow.arrival_dim_zero
#print axioms SectorNonvanishingShadow.arrival_shape
#print axioms SectorNonvanishingShadow.banked_place2_cells
#print axioms SectorNonvanishingShadow.banked_odd_cells
#print axioms SectorNonvanishingShadow.pos_of_four_mul_pos
#print axioms SectorNonvanishingShadow.odd_rhs_pos
#print axioms SectorNonvanishingShadow.place2_rhs_pos
#print axioms SectorNonvanishingShadow.odd_sector_pos
#print axioms SectorNonvanishingShadow.place2_sector_pos
