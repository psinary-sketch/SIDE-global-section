/-
  THE LADDER AND ITS FREE ORIENTATION · LadderOrientationShadow.lean
  ==================================================================

  Ferry 2026-08-27 (b212, the odd family). Vanilla Lean 4 (v4.29.1 pinned),
  no imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF.
  b212 reads the Fourier eigenvalue `c` by RANK across two interleaved families:
  the even ranks carry `c = ±1` and the odd ranks carry `c = ±i`, and each
  family's signs ALTERNATE (b211 for the even family, b212 for the odd).
  The ladder claim is that `c` runs as `ε·i^k`.

  ### THE TWO WRONSKIAN IDENTITIES GIVE EACH FAMILY'S ALTERNATION SEPARATELY.
  ### THEY DO NOT GIVE THE RELATIVE PHASE BETWEEN THE TWO FAMILIES.
  This file decides exactly what that costs:

    (1) `steps_i` (each step multiplies by `i`) ⟹ the sequence IS `ε·i^k`;
    (2) `steps_i` ⟹ `alt2` (each family alternates) — the derivable direction;
    (3) ### **THE CONVERSE FAILS.** `alt2` alone does NOT give the ladder — a
        witness satisfying `alt2` but not `steps_i` is exhibited;
    (4) `alt2` PLUS "the first step is `±i`" gives the ladder ### **UP TO
        ORIENTATION AND NO FURTHER** — both orientations occur, and both are
        exhibited.

  ### SO THE MISSING STEP OF b212's CLAUSE (e) IS NOT A CAVEAT HERE. IT IS A
  ### DECIDED FACT: the data fixes the ladder's FORM and leaves `ε` and the
  ### ORIENTATION free, and (3) and (4) are what "free" means.

  ### WHAT IT IS NOT.
  · NOT the computation, and NOT the derivation. Nothing here knows what an
    eigenvalue, a Fourier transform or a Sonin space is.
  · NOT a claim that the corpus's `c` steps by `i`. ### THAT IS PRECISELY THE
    ### STEP THIS FILE SHOWS THE DATA DOES NOT SUPPLY.
  · NOT a duplicate of `AlternationShadow` (row 83, global sign) or
    `SignTransferShadow` (row 84, transfer between factors). Those are about
    `±1`; this is about the fourth roots and the phase between two families.

  Bank: relay `data/b212_odd_family.txt`.
-/

namespace LadderOrientationShadow

/-- the fourth roots of unity, hand-built: `1`, `i`, `-1`, `-i`. -/
inductive U4 where
  | one
  | i
  | m1
  | mi
deriving DecidableEq

open U4

/-- multiplication, given as a table so every law below is `rfl` per case. -/
def mul : U4 → U4 → U4
  | one, y => y
  | i,   one => i
  | i,   i   => m1
  | i,   m1  => mi
  | i,   mi  => one
  | m1,  one => m1
  | m1,  i   => mi
  | m1,  m1  => one
  | m1,  mi  => i
  | mi,  one => mi
  | mi,  i   => one
  | mi,  m1  => i
  | mi,  mi  => m1

theorem mul_one : ∀ x, mul x one = x := by intro x; cases x <;> rfl
theorem mul_comm : ∀ x y, mul x y = mul y x := by intro x y; cases x <;> cases y <;> rfl
theorem mul_left_comm : ∀ x y z, mul x (mul y z) = mul y (mul x z) := by
  intro x y z; cases x <;> cases y <;> cases z <;> rfl
theorem i_i : mul i i = m1 := rfl
theorem mi_mi : mul mi mi = m1 := rfl

/-- `i^k`. -/
def ipow : Nat → U4
  | 0 => one
  | (n + 1) => mul i (ipow n)

/-- `(-i)^k` — the other orientation. -/
def impow : Nat → U4
  | 0 => one
  | (n + 1) => mul mi (impow n)

/-- each step multiplies by `i`: the ladder. -/
def StepsI (c : Nat → U4) : Prop := ∀ k, c (k + 1) = mul i (c k)

/-- each step multiplies by `-i`: the other orientation. -/
def StepsMI (c : Nat → U4) : Prop := ∀ k, c (k + 1) = mul mi (c k)

/-- two steps negate: ### EACH FAMILY ALTERNATES. This is what the two
    Wronskian identities give, and all they give. -/
def Alt2 (c : Nat → U4) : Prop := ∀ k, c (k + 2) = mul m1 (c k)

/-! ### THE POLARITY CONTROLS, FIRST. -/

theorem u4_distinct_one_m1 : one ≠ m1 := by decide
theorem u4_distinct_i_mi : i ≠ mi := by decide
theorem control_i_not_mi : mul i one ≠ mul mi one := by decide

/-! ### (1) THE LADDER IS `ε · i^k`. -/

theorem ladder_form (c : Nat → U4) (h : StepsI c) : ∀ k, c k = mul (c 0) (ipow k)
  | 0 => (mul_one (c 0)).symm
  | (k + 1) => by
      have ih := ladder_form c h k
      show c (k + 1) = mul (c 0) (mul i (ipow k))
      rw [h k, ih, mul_left_comm]

theorem ladder_form_mi (c : Nat → U4) (h : StepsMI c) : ∀ k, c k = mul (c 0) (impow k)
  | 0 => (mul_one (c 0)).symm
  | (k + 1) => by
      have ih := ladder_form_mi c h k
      show c (k + 1) = mul (c 0) (mul mi (impow k))
      rw [h k, ih, mul_left_comm]

/-! ### (2) THE LADDER IMPLIES EACH FAMILY ALTERNATES — the derivable direction. -/

theorem alt2_of_stepsI (c : Nat → U4) (h : StepsI c) : Alt2 c := by
  intro k
  show c (k + 1 + 1) = mul m1 (c k)
  rw [h (k + 1), h k]
  cases (c k) <;> rfl

theorem alt2_of_stepsMI (c : Nat → U4) (h : StepsMI c) : Alt2 c := by
  intro k
  show c (k + 1 + 1) = mul m1 (c k)
  rw [h (k + 1), h k]
  cases (c k) <;> rfl

/-! ### (3) ### THE CONVERSE FAILS — AND THIS IS THE FILE'S POINT.

  `bad` alternates in each family and is NOT the `i`-ladder. So "both families
  alternate" is STRICTLY WEAKER than the ladder, and the gap is the relative
  phase. -/

def bad : Nat → U4
  | 0 => one
  | 1 => mi
  | (n + 2) => mul m1 (bad n)

theorem bad_alt2 : Alt2 bad := fun _ => rfl

theorem bad_not_stepsI : ¬ StepsI bad := by
  intro h
  have h0 : bad 1 = mul i (bad 0) := h 0
  exact absurd h0 (by decide)

/-- ### SO `Alt2` DOES NOT IMPLY `StepsI`. Stated as its own terminal because
    it is the claim clause (e) rests on. -/
theorem alt2_does_not_imply_stepsI :
    ∃ c : Nat → U4, Alt2 c ∧ ¬ StepsI c :=
  ⟨bad, bad_alt2, bad_not_stepsI⟩

/-! ### (4) `Alt2` PLUS A FIRST STEP OF `±i` GIVES THE LADDER, UP TO ORIENTATION.

  ### AND NO FURTHER: `bad` above satisfies the hypothesis with the `-i` branch,
  ### and `ipow` satisfies it with the `+i` branch. ### BOTH BRANCHES OCCUR. -/

theorem stepsI_of_alt2 (c : Nat → U4) (hA : Alt2 c) (h1 : c 1 = mul i (c 0)) : StepsI c
  | 0 => h1
  | (k + 1) => by
      have ih := stepsI_of_alt2 c hA h1 k
      show c (k + 1 + 1) = mul i (c (k + 1))
      rw [hA k, ih]
      cases (c k) <;> rfl

theorem stepsMI_of_alt2 (c : Nat → U4) (hA : Alt2 c) (h1 : c 1 = mul mi (c 0)) : StepsMI c
  | 0 => h1
  | (k + 1) => by
      have ih := stepsMI_of_alt2 c hA h1 k
      show c (k + 1 + 1) = mul mi (c (k + 1))
      rw [hA k, ih]
      cases (c k) <;> rfl

/-- ### THE DICHOTOMY: with each family alternating and the first step a
    quarter-turn either way, the sequence IS `ε·i^k` or `ε·(−i)^k` —
    ### **AND THE DATA DOES NOT SAY WHICH.** -/
theorem ladder_up_to_orientation (c : Nat → U4) (hA : Alt2 c)
    (h1 : c 1 = mul i (c 0) ∨ c 1 = mul mi (c 0)) :
    (∀ k, c k = mul (c 0) (ipow k)) ∨ (∀ k, c k = mul (c 0) (impow k)) :=
  match h1 with
  | Or.inl e => Or.inl (ladder_form c (stepsI_of_alt2 c hA e))
  | Or.inr e => Or.inr (ladder_form_mi c (stepsMI_of_alt2 c hA e))

/-! ### BOTH BRANCHES ARE INHABITED — so the disjunction is not decoration. -/

theorem ipow_stepsI : StepsI ipow := fun _ => rfl
theorem ipow_alt2 : Alt2 ipow := alt2_of_stepsI ipow ipow_stepsI
theorem bad_first_step_is_mi : bad 1 = mul mi (bad 0) := by decide
theorem ipow_first_step_is_i : ipow 1 = mul i (ipow 0) := by decide

/-- ### THE TWO ORIENTATIONS ARE GENUINELY DIFFERENT SEQUENCES. -/
theorem orientations_differ : ipow 1 ≠ impow 1 := by decide

end LadderOrientationShadow

#print axioms LadderOrientationShadow.mul_one
#print axioms LadderOrientationShadow.mul_comm
#print axioms LadderOrientationShadow.mul_left_comm
#print axioms LadderOrientationShadow.u4_distinct_one_m1
#print axioms LadderOrientationShadow.u4_distinct_i_mi
#print axioms LadderOrientationShadow.control_i_not_mi
#print axioms LadderOrientationShadow.ladder_form
#print axioms LadderOrientationShadow.ladder_form_mi
#print axioms LadderOrientationShadow.alt2_of_stepsI
#print axioms LadderOrientationShadow.alt2_of_stepsMI
#print axioms LadderOrientationShadow.bad_alt2
#print axioms LadderOrientationShadow.bad_not_stepsI
#print axioms LadderOrientationShadow.alt2_does_not_imply_stepsI
#print axioms LadderOrientationShadow.stepsI_of_alt2
#print axioms LadderOrientationShadow.stepsMI_of_alt2
#print axioms LadderOrientationShadow.ladder_up_to_orientation
#print axioms LadderOrientationShadow.ipow_stepsI
#print axioms LadderOrientationShadow.ipow_alt2
#print axioms LadderOrientationShadow.bad_first_step_is_mi
#print axioms LadderOrientationShadow.ipow_first_step_is_i
#print axioms LadderOrientationShadow.orientations_differ
