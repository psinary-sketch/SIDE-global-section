/-
  THE ALTERNATION ARGUMENT'S CORE · AlternationShadow.lean
  =========================================================

  Ferry 2026-08-26 (b207, the alternation at our parameter). Vanilla Lean 4
  (v4.29.1 pinned), no imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF.
  b207's verdict rests on two statements, and the ferry requires them SHOWN
  rather than asserted:
    (1) if every sign carries an unknown GLOBAL factor `e = ±1`, the sequence
        alternates exactly when the original does — because `e` is CONSTANT
        across the sequence;
    (2) an alternating sign sequence takes BOTH values.
  Together: ### "BOTH VALUES OF c OCCUR" IS INVARIANT UNDER EXACTLY THE FREEDOM
  ### b205's UNEXPLAINED SIGN DISAGREEMENT LEAVES OPEN.

  ### WHAT IT IS NOT.
  · It is NOT the computation. The computation is at bench grade in
    `relay/data/b207_alternation.txt`, and nothing here touches an eigenvalue,
    a transform, or a Sonin space.
  · It does NOT establish that the corpus's sequence alternates. That is a
    measured fact about a finite sweep, and it lives at its own grade.
  · ### A SHADOW OF THE ARGUMENT IS NOT THE ARGUMENT'S SUBJECT, and this header
    ### says so rather than leaving a reader to infer it.

  Bank: relay `data/b207_alternation.txt`.
-/

namespace AlternationShadow

/-- a sign sequence alternates when each term is the negation of the last. -/
def Alternates (s : Nat → Int) : Prop := ∀ i, s (i + 1) = -s i

/-! ### THE POLARITY CONTROLS, FIRST.

  A theorem about alternating sequences proved without a witness that FAILS to
  alternate is a theorem nobody has tested. ### So the failing case is decided
  before the theorems are stated. -/

/-- a witness that DOES alternate. -/
def flip : Nat → Int := fun i => if i % 2 = 0 then 1 else -1

/-- and one that does NOT — so `Alternates` genuinely selects. -/
def const1 : Nat → Int := fun _ => 1

theorem flip_alternates_at_0 : flip 1 = -flip 0 := by decide

theorem const1_fails_at_0 : const1 1 ≠ -const1 0 := by decide

/-- ### AND THE TWO VALUES ARE DISTINCT — without this, "both values occur"
    would be consistent with there being only one. -/
theorem signs_distinct : (1 : Int) ≠ -1 := by decide

/-! ### (1) ALTERNATION IS INVARIANT UNDER A GLOBAL SIGN.

  ### A GLOBAL SIGN ERROR **IS** NEGATION, so the statement is phrased in the
  ### operation itself rather than in multiplication by a scalar. ### That is
  ### both closer to what b205 left open and cheaper: it needs no arithmetic
  ### lemma at all, and the print below shows the difference.
  ### THE POINT IS THAT THE SIGN DOES NOT DEPEND ON `i`. ### A factor varying
  ### with the index would not be a GLOBAL sign error and is not covered. -/

theorem alternates_neg (s : Nat → Int) (h : Alternates s) :
    Alternates (fun i => -s i) := by
  intro i
  show -s (i + 1) = -(-s i)
  rw [h i]

/-! ### (2) AN ALTERNATING SEQUENCE TAKES BOTH VALUES. -/

theorem alternates_both (s : Nat → Int) (h : Alternates s) (h0 : s 0 = 1) :
    (∃ i, s i = 1) ∧ (∃ i, s i = -1) :=
  ⟨⟨0, h0⟩, ⟨1, by rw [h 0, h0]⟩⟩

theorem alternates_both' (s : Nat → Int) (h : Alternates s) (h0 : s 0 = -1) :
    (∃ i, s i = 1) ∧ (∃ i, s i = -1) :=
  ⟨⟨1, by rw [h 0, h0]; decide⟩, ⟨0, h0⟩⟩

/-! ### THE TWO COMBINED — the statement the verdict actually leans on. -/

/-- ### IF A SEQUENCE OF `±1`s ALTERNATES, THEN SO DOES ITS GLOBAL NEGATION,
    AND BOTH VALUES STILL OCCUR IN EITHER. ### So a global sign error cannot
    turn “both values occur” into “one value occurs”. -/
theorem both_values_survive_global_sign
    (s : Nat → Int) (h : Alternates s) (h0 : s 0 = 1 ∨ s 0 = -1) :
    ((∃ i, s i = 1) ∧ (∃ i, s i = -1))
      ∧ ((∃ i, (fun j => -s j) i = 1) ∧ (∃ i, (fun j => -s j) i = -1)) := by
  have hn : Alternates (fun i => -s i) := alternates_neg s h
  match h0 with
  | Or.inl e =>
      exact ⟨alternates_both s h e,
             alternates_both' (fun i => -s i) hn (by show -s 0 = -1; rw [e])⟩
  | Or.inr e =>
      exact ⟨alternates_both' s h e,
             alternates_both (fun i => -s i) hn (by show -s 0 = 1; rw [e]; decide)⟩

end AlternationShadow

#print axioms AlternationShadow.flip_alternates_at_0
#print axioms AlternationShadow.const1_fails_at_0
#print axioms AlternationShadow.signs_distinct
#print axioms AlternationShadow.alternates_neg
#print axioms AlternationShadow.alternates_both
#print axioms AlternationShadow.alternates_both'
#print axioms AlternationShadow.both_values_survive_global_sign
