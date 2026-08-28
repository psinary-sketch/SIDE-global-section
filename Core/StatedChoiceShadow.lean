/-
  THE STATED CHOICE, AS A CHOICE FUNCTION · StatedChoiceShadow.lean
  =================================================================

  Ferry 2026-08-28 (b226, the stated choice). Vanilla Lean 4 (v4.29.1 pinned),
  no imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF — AND WHAT IT IS **NOT**.
  b225's ruling opened a plan: term 3 on a STATED CHOICE of norm-one unit per
  finite place in `E₁` at the level limit. b226 states that choice. This file
  shadows the part of the statement that is **finite-decidable**:

    ### **the CHOICE FUNCTION — that the level this act picks at each stated
    place really is a level where `E₁` is nonzero, and really is the LOWEST
    such level — and that norm-one units make the C₀ deviation sum exactly 0.**

  ### **IT SHADOWS NO TRACE, NO VALUE, AND NO TERM-2 STATEMENT.** The trace is
  the next act's business, by the ferry's own scope line.
  ### **AND IT USES NO INCLUSION MAP BETWEEN LEVELS** — none is defined here,
  because the plan does not use one.

  ### THE STAND-IN, DECLARED. `d₁` is the record's own closed form (b198 (I3),
  owner correspondence row 36 / b57), carried here as a `Nat` function:
    ### place 2 : `4d = q(q−2)`     ### odd p : `4d = (q−1)²`     with `q = pⁿ`.
  b223 re-derived those values exactly in `ℤ[ζ_N]` at 13 cells and they agreed
  13 of 13. ### **This file does not re-derive them; it reasons FROM them, and
  that is why it is a shadow and not the result.**

  ### THE POLARITY CONTROLS COME FIRST, and they are not decoration:
  `arrival_depth_is_dead` shows the positivity claim is FALSE at some cell, so
  `chosen_level_positive` is not vacuously true of everything; and
  `deviation_can_be_nonzero` shows the C₀ deviation function is not constantly
  zero, so `c0_deviation_is_zero` is measuring norm-one and not the encoding.
-/

namespace StatedChoiceShadow

/-- `q = pⁿ`. -/
def q (p n : Nat) : Nat := p ^ n

/-- `4·d₁` from the record's closed forms: `q(q−2)` at p = 2, `(q−1)²` at odd p. -/
def fourD1 (p n : Nat) : Nat :=
  if p = 2 then q p n * (q p n - 2) else (q p n - 1) * (q p n - 1)

/-- `d₁(p,n)`, the record's closed form. -/
def d1 (p n : Nat) : Nat := fourD1 p n / 4

/-- ### THE CHOICE: the level this act picks at each place —
    level 2 at p = 2, level 1 at every odd place. -/
def level (p : Nat) : Nat := if p = 2 then 2 else 1

/-- the finite places this act actually states a unit at, and checks. -/
def stated : List Nat := [2, 3, 5, 7, 11, 13]

/-- ### POLARITY CONTROL, NEGATIVE — **the arrival depth**. `d₁` really is zero
    somewhere, so the positivity theorem below is not vacuous. -/
theorem arrival_depth_is_dead : d1 2 1 = 0 := by decide

/-- ### POLARITY CONTROL, NEGATIVE — level 1 is NOT a valid choice at p = 2,
    which is exactly why `level 2 = 2`. -/
theorem level_one_fails_at_two : ¬ (0 < d1 2 (1)) := by decide

/-- ### THE CHOICE LANDS: at every stated place, the chosen level has `E₁ ≠ 0`. -/
theorem chosen_level_positive : ∀ p ∈ stated, 0 < d1 p (level p) := by decide

/-- ### AND IT IS THE **LOWEST** SUCH LEVEL: at every odd stated place level 1
    already works, and at p = 2 level 1 does not — so `level` picks the first. -/
theorem chosen_level_is_lowest :
    (∀ p ∈ stated, p ≠ 2 → 0 < d1 p 1) ∧ d1 2 1 = 0 := by decide

/-- the C₀ deviation contributed by one place, `| ‖u‖ − 1 |`, on a scale where a
    norm-one unit contributes 0. -/
def dev (norm : Nat) : Nat := if norm = 1 then 0 else 1

/-- the total deviation over a list of places. -/
def devSum : List Nat → Nat
  | [] => 0
  | x :: xs => dev x + devSum xs

/-- ### POLARITY CONTROL, NEGATIVE — the deviation sum is NOT constantly zero,
    so the theorem below measures norm-one rather than the encoding. -/
theorem deviation_can_be_nonzero : devSum [1, 2, 1] = 1 := by decide

/-- ### G-NORM, SHADOWED: norm-one at every stated place makes the C₀ deviation
    sum **exactly 0** — which converges in the strongest way available. -/
theorem c0_deviation_is_zero : devSum (stated.map (fun _ => 1)) = 0 := by decide

/-- ### AND THE CHOICE IS A FUNCTION, not a family of unrelated picks: `level`
    is single-valued, which is the whole content of "a STATED choice". -/
theorem level_is_a_function (p : Nat) (a b : Nat)
    (ha : a = level p) (hb : b = level p) : a = b := by
  rw [ha, hb]

end StatedChoiceShadow

#print axioms StatedChoiceShadow.arrival_depth_is_dead
#print axioms StatedChoiceShadow.level_one_fails_at_two
#print axioms StatedChoiceShadow.chosen_level_positive
#print axioms StatedChoiceShadow.chosen_level_is_lowest
#print axioms StatedChoiceShadow.deviation_can_be_nonzero
#print axioms StatedChoiceShadow.c0_deviation_is_zero
#print axioms StatedChoiceShadow.level_is_a_function
