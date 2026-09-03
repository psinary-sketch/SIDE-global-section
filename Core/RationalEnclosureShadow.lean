/-
  b302 · RationalEnclosureShadow.lean — THE VANILLA LEG (zero axioms)
  ===================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES, AND — far more importantly — WHAT IT DOES NOT.

  IT COMPILES ONE ARITHMETIC FACT ABOUT TWO EXPLICIT RATIONALS:

      WITH DENOMINATOR 10^20, THE NUMERATORS 70710678118654752440 AND
      70710678118654752441 SATISFY  2·lo² < den²  AND  den² < 2·hi².

  THAT IS THE WHOLE CONTENT. Every quantity in it is a decidable comparison of natural
  numbers, and the terminals NAME THE DENOMINATOR AND THE CRITERION IN THEIR OWN
  STATEMENTS so a reader never has to consult a comment to learn the scope.

  WHY THE SQUARING CRITERION AND NOT A NUMBER. Vanilla Lean has no real numbers and no
  square roots. THE FILE THEREFORE DOES NOT MENTION 1/√2 ANYWHERE IN A STATEMENT — it
  decides the two INTEGER inequalities that the elementary equivalence

      for positive rationals a/b :   a/b < 1/√2  ⟺  2a² < b²

  turns into a statement about that constant. THAT EQUIVALENCE IS NOT PROVED HERE AND
  IS NOT CLAIMED HERE; it is elementary, it is about real numbers, and a reader supplies
  it. WHAT THE KERNEL CERTIFIES IS THE INTEGER SIDE, EXACTLY AND ONLY.

  WHAT IS NOT COMPILED HERE, AND MUST NOT BE READ INTO IT:

    · ANYTHING ABOUT A NORM, A UNIT VECTOR, OR A LOCAL HILBERT SPACE. The constant
      1 − 1/√2 arises elsewhere in the programme as a possible deviation term. NOTHING
      IN THIS FILE MENTIONS THAT, and no terminal name here refers to it. The file
      certifies an enclosure; where the enclosed number is used is not its business.
    · THAT THE ENCLOSURE IS TIGHT IN ANY SENSE BEYOND ITS STATED WIDTH. It is one unit
      of the denominator wide, and `enclosure_is_one_unit_of_the_denominator_wide` says
      exactly that and no more.
    · THAT 1/√2 IS IRRATIONAL, or that no rational equals it. NO FINITE OBJECT HERE
      BEARS ON THAT and none is claimed to.
    · ANY ROUTE, ANY AGGREGATION. M-2 is owed and stays owed.
    · ANYTHING ABOUT `h2`, which stands exactly where the deposit left it.

  THE UNAVAILABLE ARM, AND WHY IT IS DECIDED RATHER THAN DESCRIBED. A polarity control
  normally shows that a criterion REFUSES something. At denominator 1 there is a place
  where no such control can exist: the tightest enclosure the criterion admits is the
  WHOLE unit interval, because there is no natural number strictly between 0 and 1 to
  narrow it with. `at_denominator_one_the_enclosure_is_the_whole_unit_interval` decides
  all four facts that say so — 0/1 is below, 1/1 is above, and NEITHER can be moved.
  THE ARM IS UNAVAILABLE AT THAT DENOMINATOR AND THE FILE DECIDES THE DEGENERACY
  INSTEAD OF ASSERTING IT IN A COMMENT.

  NO FLOATING POINT ANYWHERE. NO DIVISION ANYWHERE. Every numeral below is a `Nat`.
-/

namespace B302

/-! ### THE CRITERION. Two Boolean predicates on natural numbers, and nothing else. -/

/-- `below a b` decides `2a² < b²`. For positive `a, b` this is the integer form of
    `a/b < 1/√2`; THE EQUIVALENCE IS THE READER'S AND IS NOT PROVED IN THIS FILE. -/
def below (a b : Nat) : Bool := 2 * a * a < b * b

/-- `above c d` decides `d² < 2c²` — the integer form of `c/d > 1/√2`, on the same
    footing and with the same disclaimer. -/
def above (c d : Nat) : Bool := d * d < 2 * c * c

/-! ### THE POLARITY CONTROLS, FIRST. A criterion that accepts everything is not a
    criterion, and a criterion that refuses everything certifies nothing. BOTH
    DIRECTIONS ARE DECIDED BEFORE ANY CLAIM IS MADE WITH THE CRITERION. -/

theorem criterion_refuses_a_lower_bound_that_is_too_large :
    below 8 10 = false := by decide

theorem criterion_refuses_an_upper_bound_that_is_too_small :
    above 7 10 = false := by decide

theorem criterion_accepts_a_correct_lower_bound :
    below 7 10 = true := by decide

theorem criterion_accepts_a_correct_upper_bound :
    above 8 10 = true := by decide

/-! ### THE UNAVAILABLE ARM, DECIDED. At denominator 1 the criterion's tightest
    enclosure is the whole unit interval and no narrower control exists there. -/

theorem at_denominator_one_the_enclosure_is_the_whole_unit_interval :
    below 0 1 = true ∧ above 1 1 = true ∧ below 1 1 = false ∧ above 0 1 = false := by
  decide

/-! ### THE EXPLICIT RATIONALS. The denominator is `10^20`, written out. -/

/-- The denominator, `10^20`. -/
def den : Nat := 100000000000000000000

/-- The lower numerator. -/
def loNum : Nat := 70710678118654752440

/-- The upper numerator. -/
def hiNum : Nat := 70710678118654752441

/-- `den - hiNum`: the numerator of the lower end of `1 - hi/den`. -/
def devLoNum : Nat := den - hiNum

/-- `den - loNum`: the numerator of the upper end of `1 - lo/den`. -/
def devHiNum : Nat := den - loNum

/-! ### THE NOT-DEAD WITNESS. An enclosure whose ends coincide, or whose ends are the
    wrong way round, would satisfy nothing worth stating. Both are excluded here. -/

theorem enclosure_is_one_unit_of_the_denominator_wide :
    hiNum = loNum + 1 := by decide

theorem enclosure_ends_are_strictly_ordered :
    loNum < hiNum := by decide

theorem complement_numerators_are_strictly_positive_and_below_the_denominator :
    0 < devLoNum ∧ devHiNum < den := by decide

/-! ### THE TERMINALS. -/

/-- THE ENCLOSURE. The two explicit numerators over `10^20` satisfy the squaring
    criterion in both directions. -/
theorem explicit_numerators_over_ten_to_the_twenty_satisfy_the_squaring_criterion :
    below loNum den = true ∧ above hiNum den = true := by decide

/-- THE COMPLEMENT'S NUMERATORS, decided as integers so a reader reconstructs the
    complementary enclosure from decided values rather than from arithmetic in prose. -/
theorem complement_numerators_over_ten_to_the_twenty_are_these_two_integers :
    devLoNum = 29289321881345247559 ∧ devHiNum = 29289321881345247560 := by decide

/-- THE COMPLEMENT ALSO SATISFIES THE CRITERION IN THE MIRRORED DIRECTION, decided
    rather than inferred: `den - hiNum` is the lower end and `den - loNum` the upper,
    and they are ordered and one unit apart, exactly as the originals are. -/
theorem complement_enclosure_is_one_unit_wide_and_strictly_ordered :
    devHiNum = devLoNum + 1 ∧ devLoNum < devHiNum := by decide

/-! ### THE AXIOM PROFILE, PRINTED BY THIS FILE ITSELF.

    b227's standard: a claimed compile is reported ONLY from its printed profile.
    These prints live in the banked file so the profile is produced by compiling the
    artefact that was banked — not by compiling a copy of it. -/

#print axioms B302.criterion_refuses_a_lower_bound_that_is_too_large
#print axioms B302.criterion_refuses_an_upper_bound_that_is_too_small
#print axioms B302.criterion_accepts_a_correct_lower_bound
#print axioms B302.criterion_accepts_a_correct_upper_bound
#print axioms B302.at_denominator_one_the_enclosure_is_the_whole_unit_interval
#print axioms B302.enclosure_is_one_unit_of_the_denominator_wide
#print axioms B302.enclosure_ends_are_strictly_ordered
#print axioms B302.complement_numerators_are_strictly_positive_and_below_the_denominator
#print axioms B302.explicit_numerators_over_ten_to_the_twenty_satisfy_the_squaring_criterion
#print axioms B302.complement_numerators_over_ten_to_the_twenty_are_these_two_integers
#print axioms B302.complement_enclosure_is_one_unit_wide_and_strictly_ordered

end B302
