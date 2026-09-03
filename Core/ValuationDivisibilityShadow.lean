/-
  b303 · ValuationDivisibilityShadow.lean — THE VANILLA LEG (zero axioms)
  ======================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES, AND — far more importantly — WHAT IT DOES NOT.

  IT COMPILES ONE ARITHMETIC FACT ABOUT NATURAL NUMBERS, AT FIVE EXPLICIT PAIRS (p, n):

      OVER THE RANGE m < p^(2n), THE PREDICATE "THE p-ADIC VALUATION OF m IS AT LEAST n"
      AND THE PREDICATE "p^n DIVIDES m" AGREE ON EVERY m.

  THAT IS THE WHOLE CONTENT. Both sides are decidable predicates on natural numbers, and
  the terminals NAME THE PAIR (p, n) IN THEIR OWN STATEMENTS so a reader never has to
  consult a comment to learn the scope.

  WHY THE TWO PREDICATES ARE DEFINED SEPARATELY, WHICH IS THE POINT OF THE FILE. The
  valuation is computed BY REPEATED DIVISION (`vpAux`, fuel-bounded and structurally
  recursive). The divisibility test is a SINGLE MODULO (`dvdPow`). NEITHER IS DEFINED IN
  TERMS OF THE OTHER. Had the valuation been defined as "the largest k with p^k ∣ m",
  the agreement below would be a tautology wearing the costume of a check.

  THE ZERO CASE IS HANDLED EXPLICITLY AND IS THE ONE THAT BITES. 0 is divisible by every
  power, and its valuation is not a natural number. `valGe` therefore admits 0 outright
  rather than asking `vpAux` about it, and `valuation_of_zero_is_admitted_at_every_index`
  decides that this is what it does.

  WHAT IS NOT COMPILED HERE, AND MUST NOT BE READ INTO IT:

    · ANY STATEMENT ABOUT A FUNCTION SPACE, A TRANSFORM, A SUBSPACE, OR A DIMENSION.
      These predicates cut out a set of INDICES. What is done elsewhere with such a set
      is not this file's business and no terminal name here refers to it.
    · ANY STATEMENT ABOUT A SECOND CONDITION OF ANY KIND. The file decides ONE predicate
      identity. A construction that pairs two such conditions is not modelled here.
    · ANYTHING ABOUT A METRIC, A CUTOFF, A SCALE, OR A REAL NUMBER. Vanilla Lean has no
      real numbers and this file introduces none. EVERY NUMERAL BELOW IS A `Nat`.
    · ANY CLAIM AT A PAIR (p, n) NOT NAMED IN A TERMINAL. The range law governs: these
      are finite-instance statements at the five stated pairs and no wider. NOTHING IS
      CLAIMED ABOUT A GENERIC p, A GENERIC n, OR A LIMIT.
    · ANY ROUTE, ANY AGGREGATION. M-2 is owed and stays owed.
    · ANYTHING ABOUT `h2`, which stands exactly where the deposit left it.

  THE FUEL, AND WHY IT IS DECIDED RATHER THAN ASSERTED. `vpAux` is fuel-bounded so that
  it is structurally recursive, and a fuel that ran out would SILENTLY UNDER-REPORT a
  valuation — which is exactly how this file could agree with itself and be wrong.
  `fuel_is_not_binding_on_the_tested_range_*` decides that doubling the fuel changes no
  answer on the range actually tested. THE GUARD IS DECIDED, NOT PROMISED IN A COMMENT.

  THE POLARITY CONTROLS COME FIRST, BECAUSE A PREDICATE PAIR THAT AGREED EVERYWHERE FOR
  TRIVIAL REASONS WOULD PASS EVERY TEST BELOW. `the_two_predicates_disagree_one_index_out_*`
  decides that shifting the valuation threshold by one BREAKS the agreement — so the
  agreement at the stated threshold is a fact about that threshold and not about two
  predicates that would agree with anything.

  NO FLOATING POINT ANYWHERE. NO DIVISION OF ANYTHING BUT NATURALS ANYWHERE.
-/

namespace B303

/-- The p-adic valuation, by repeated division. Fuel-bounded so it is structurally
    recursive; the fuel's adequacy on each tested range is itself decided below. -/
def vpAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, p, m => if m != 0 && 2 ≤ p && m % p == 0 then 1 + vpAux f p (m / p) else 0

/-- The valuation at the working fuel. -/
def vp (p m : Nat) : Nat := vpAux 16 p m

/-- "The valuation of `m` is at least `n`". 0 is admitted outright: it is divisible by
    every power and its valuation is not a natural number. -/
def valGe (p n m : Nat) : Bool := m == 0 || n ≤ vp p m

/-- "`p^n` divides `m`". A single modulo. It never calls `vp`. -/
def dvdPow (p n m : Nat) : Bool := m % (p ^ n) == 0

/-- The two predicates agree at every index below the stated bound. -/
def agreeOn (p n bound : Nat) : Bool :=
  (List.range bound).all (fun m => valGe p n m == dvdPow p n m)

/-- The count of indices the divisibility predicate admits below the stated bound. -/
def admittedCount (p n bound : Nat) : Nat :=
  ((List.range bound).filter (fun m => dvdPow p n m)).length

/-- The same agreement, computed at double fuel, for the fuel guard. -/
def agreeOnAtFuel (fuel p n bound : Nat) : Bool :=
  (List.range bound).all (fun m => (m == 0 || n ≤ vpAux fuel p m) == dvdPow p n m)

/-- The agreement with ONE SIDE SHIFTED by one index: the valuation threshold stays at
    `n` while the divisibility exponent moves to `n+1`. This must FAIL. -/
def agreeOnShifted (p n bound : Nat) : Bool :=
  (List.range bound).all (fun m => valGe p n m == dvdPow p (n + 1) m)

-- ---------------------------------------------------------------------------
-- THE POLARITY CONTROLS, FIRST.
-- ---------------------------------------------------------------------------

/-- The valuation really is computed, at named points, and it is not constant. -/
theorem valuation_by_repeated_division_at_named_points :
    (vp 2 8 == 3 && vp 3 9 == 2 && vp 2 6 == 1 && vp 2 5 == 0 && vp 5 25 == 2) = true := by
  decide

/-- 0 is admitted at every index tested, which is the case the valuation cannot answer. -/
theorem valuation_of_zero_is_admitted_at_every_index :
    (valGe 2 1 0 && valGe 2 5 0 && valGe 3 2 0 && valGe 5 4 0) = true := by
  decide

/-- The divisibility predicate REFUSES something: it is not the constant true. -/
theorem divisibility_predicate_refuses_indices_it_should :
    (dvdPow 2 1 3 == false && dvdPow 3 2 3 == false && dvdPow 5 1 7 == false) = true := by
  decide

/-- And it ACCEPTS what it should: it is not the constant false either. -/
theorem divisibility_predicate_accepts_indices_it_should :
    (dvdPow 2 1 4 && dvdPow 3 2 9 && dvdPow 5 1 10) = true := by
  decide

/-- THE DISCRIMINATION, AND IT WAS WRONG ON THE FIRST COMPILE. Moving BOTH sides
    together changes nothing — the identity holds at every index, so a control that
    shifted `n` on both sides agreed and proved nothing. `decide` refuted it, which is
    the only reason it was caught. The control that discriminates shifts ONE side:
    the valuation threshold stays at `n`, the divisibility exponent moves to `n+1`,
    and the agreement BREAKS at every tested pair. -/
theorem the_two_predicates_disagree_when_one_side_is_shifted_at_every_tested_pair :
    (agreeOnShifted 2 1 4 == false && agreeOnShifted 2 2 16 == false
      && agreeOnShifted 3 1 9 == false && agreeOnShifted 3 2 81 == false
      && agreeOnShifted 5 1 25 == false) = true := by
  decide

/-- THE FUEL GUARD. Doubling the fuel changes no answer on any tested range, so no
    valuation below was silently truncated by running out of fuel. -/
theorem fuel_is_not_binding_on_the_tested_ranges :
    (agreeOnAtFuel 16 2 1 4 == agreeOnAtFuel 32 2 1 4
      && agreeOnAtFuel 16 2 2 16 == agreeOnAtFuel 32 2 2 16
      && agreeOnAtFuel 16 3 1 9 == agreeOnAtFuel 32 3 1 9
      && agreeOnAtFuel 16 3 2 81 == agreeOnAtFuel 32 3 2 81
      && agreeOnAtFuel 16 5 1 25 == agreeOnAtFuel 32 5 1 25) = true := by
  decide

/-- The admitted set is neither empty nor everything, at every tested pair. An identity
    between two predicates that both admitted nothing would be true and worthless. -/
theorem admitted_set_is_a_proper_nonempty_subset_at_every_tested_pair :
    (admittedCount 2 1 4 == 2 && admittedCount 2 2 16 == 4 && admittedCount 3 1 9 == 3
      && admittedCount 3 2 81 == 9 && admittedCount 5 1 25 == 5) = true := by
  decide

-- ---------------------------------------------------------------------------
-- THE TERMINALS. ONE PER PAIR (p, n), THE PAIR NAMED IN THE STATEMENT.
-- ---------------------------------------------------------------------------

/-- At p = 2, n = 1: over m < 2^2, "valuation at least 1" and "2^1 divides m" agree. -/
theorem valuation_and_divisibility_agree_over_the_range_at_p_two_n_one :
    agreeOn 2 1 4 = true := by decide

/-- At p = 2, n = 2: over m < 2^4, "valuation at least 2" and "2^2 divides m" agree. -/
theorem valuation_and_divisibility_agree_over_the_range_at_p_two_n_two :
    agreeOn 2 2 16 = true := by decide

/-- At p = 3, n = 1: over m < 3^2, "valuation at least 1" and "3^1 divides m" agree. -/
theorem valuation_and_divisibility_agree_over_the_range_at_p_three_n_one :
    agreeOn 3 1 9 = true := by decide

/-- At p = 3, n = 2: over m < 3^4, "valuation at least 2" and "3^2 divides m" agree. -/
theorem valuation_and_divisibility_agree_over_the_range_at_p_three_n_two :
    agreeOn 3 2 81 = true := by decide

/-- At p = 5, n = 1: over m < 5^2, "valuation at least 1" and "5^1 divides m" agree. -/
theorem valuation_and_divisibility_agree_over_the_range_at_p_five_n_one :
    agreeOn 5 1 25 = true := by decide

end B303

-- The polarity controls print FIRST, as they appear first in the file.
#print axioms B303.valuation_by_repeated_division_at_named_points
#print axioms B303.valuation_of_zero_is_admitted_at_every_index
#print axioms B303.divisibility_predicate_refuses_indices_it_should
#print axioms B303.divisibility_predicate_accepts_indices_it_should
#print axioms B303.the_two_predicates_disagree_when_one_side_is_shifted_at_every_tested_pair
#print axioms B303.fuel_is_not_binding_on_the_tested_ranges
#print axioms B303.admitted_set_is_a_proper_nonempty_subset_at_every_tested_pair
#print axioms B303.valuation_and_divisibility_agree_over_the_range_at_p_two_n_one
#print axioms B303.valuation_and_divisibility_agree_over_the_range_at_p_two_n_two
#print axioms B303.valuation_and_divisibility_agree_over_the_range_at_p_three_n_one
#print axioms B303.valuation_and_divisibility_agree_over_the_range_at_p_three_n_two
#print axioms B303.valuation_and_divisibility_agree_over_the_range_at_p_five_n_one
