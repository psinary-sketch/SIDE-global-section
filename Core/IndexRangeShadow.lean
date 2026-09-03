/-
  b304 · IndexRangeShadow.lean — THE VANILLA LEG (zero axioms)
  ============================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES, AND — far more importantly — WHAT IT DOES NOT.

  IT COMPILES ONE ARITHMETIC FACT ABOUT TWO RANGES OF NATURAL NUMBERS:

      WRITING  R(n) = [1, …, n]  AND  B(n) = [1, …, n−1],
      AT n = 1 THE FIRST IS THE SINGLE POINT [1], THE SECOND IS EMPTY,
      AND THAT SINGLE POINT IS EQUAL TO n.

  THAT IS THE WHOLE CONTENT. Both sides are explicit finite lists of naturals, and the
  terminals NAME THE BOUND IN THEIR OWN STATEMENTS so a reader never has to consult a
  comment to learn the scope.

  WHY THE TWO RANGES ARE DEFINED SEPARATELY AND NEITHER IN TERMS OF THE OTHER. `R` is
  built from `List.range n` and `B` from `List.range (n−1)`. Defining `B` as "`R` with its
  last element dropped" would make the emptiness at n = 1 a fact about a drop operation
  rather than about the bound, and the polarity control below would then be testing the
  drop.

  THE `n = 0` CASE IS DECIDED RATHER THAN LEFT AT THE EDGE. In `Nat`, `0 − 1 = 0`, so
  `B(0)` and `B(1)` are both empty for DIFFERENT reasons — truncated subtraction in one
  case, an empty bound in the other. `both_ranges_are_empty_at_zero` decides that state
  explicitly so that no later reader mistakes the n = 1 emptiness for a truncation
  artifact.

  WHAT IS NOT COMPILED HERE, AND MUST NOT BE READ INTO IT:

    · ANY STATEMENT ABOUT A PRIME, A PLACE, A TOWER, A LEVEL, A SPACE, A TRACE, A SUM,
      OR AN AGGREGATION. These are two lists of naturals. What is indexed BY such a range
      elsewhere is not this file's business and no terminal name here refers to it.
    · ANY STATEMENT THAT SOMETHING CANNOT BE SUPPLIED OVER A ONE-POINT RANGE. That is an
      argument about other objects and it is made in prose elsewhere, not certified here.
      THIS FILE CERTIFIES THE SHAPE OF THE RANGE AND NOTHING THAT FOLLOWS FROM IT.
    · ANY CLAIM AT A BOUND NOT NAMED IN A TERMINAL. The range law governs: these are
      finite-instance statements at the stated bounds and no wider.
    · ANY ROUTE, ANY AGGREGATION. M-2 is owed and stays owed.
    · ANYTHING ABOUT `h2`, which stands exactly where the deposit left it.

  THE POLARITY CONTROLS COME FIRST, BECAUSE A PAIR OF RANGES THAT WERE EMPTY FOR TRIVIAL
  REASONS WOULD SATISFY EVERYTHING BELOW. `below_top_range_is_nonempty_from_two_up`
  decides that `B` is NOT always empty, and `index_range_grows_with_its_bound` decides
  that `R` is not the constant singleton.

  NO FLOATING POINT ANYWHERE. EVERY NUMERAL BELOW IS A `Nat`.
-/

namespace B304

/-- `R n = [1, …, n]`: the full index range up to the bound `n`. -/
def R (n : Nat) : List Nat := (List.range n).map (fun i => i + 1)

/-- `B n = [1, …, n−1]`: the range strictly below the bound. Built from its own bound,
    never as `R n` with an element removed. -/
def B (n : Nat) : List Nat := (List.range (n - 1)).map (fun i => i + 1)

/-- The largest entry of a list of naturals, `0` on the empty list. -/
def topOf (l : List Nat) : Nat := l.foldl max 0

-- ---------------------------------------------------------------------------
-- THE POLARITY CONTROLS, FIRST.
-- ---------------------------------------------------------------------------

/-- `B` is NOT always empty: from bound 2 upward it has entries. Without this, every
    emptiness statement below would be satisfied by a definition that never produces
    anything. -/
theorem below_top_range_is_nonempty_from_two_up :
    (B 2 == [1] && B 3 == [1, 2] && B 4 == [1, 2, 3]) = true := by decide

/-- `R` is not the constant singleton: it grows with its bound. -/
theorem index_range_grows_with_its_bound :
    (R 1 == [1] && R 2 == [1, 2] && R 3 == [1, 2, 3] && R 4 == [1, 2, 3, 4]) = true := by decide

/-- The two ranges have the lengths their bounds name, at the stated bounds. -/
theorem the_two_ranges_have_the_lengths_their_bounds_name :
    ((R 1).length == 1 && (B 1).length == 0 && (R 2).length == 2 && (B 2).length == 1
      && (R 3).length == 3 && (B 3).length == 2 && (R 4).length == 4
      && (B 4).length == 3) = true := by decide

/-- `topOf` really reports the largest entry, and `0` on the empty list. -/
theorem top_of_reports_the_largest_entry :
    (topOf [1, 2, 3] == 3 && topOf [1] == 1 && topOf ([] : List Nat) == 0
      && topOf [2, 7, 5] == 7) = true := by decide

/-- THE EDGE, DECIDED RATHER THAN LEFT AT THE EDGE. At bound 0 both ranges are empty,
    and `B` is empty there because `Nat` subtraction truncates, not because the bound is
    one. Deciding this is what stops a later reader reading the bound-1 emptiness below
    as a truncation artifact. -/
theorem both_ranges_are_empty_at_zero :
    (R 0 == ([] : List Nat) && B 0 == ([] : List Nat) && (0 - 1 : Nat) == 0) = true := by decide

-- ---------------------------------------------------------------------------
-- THE TERMINALS. THE BOUND IS NAMED IN EVERY STATEMENT.
-- ---------------------------------------------------------------------------

/-- At bound 1 the index range is the single point `[1]`. -/
theorem index_range_at_bound_one_is_a_single_point :
    (R 1 == [1] && (R 1).length == 1) = true := by decide

/-- At bound 1 the range strictly below the bound is empty. -/
theorem below_top_range_at_bound_one_is_empty :
    (B 1 == ([] : List Nat) && (B 1).length == 0) = true := by decide

/-- At bound 1 that single point IS the top of the range, and the top is the bound. -/
theorem the_single_point_at_bound_one_is_the_top_and_the_top_is_the_bound :
    (topOf (R 1) == 1 && (R 1) == [topOf (R 1)]) = true := by decide

/-- And the top of the range is the bound at every stated bound, so the coincidence at
    bound 1 is the coincidence of the top with a one-point range and not an accident of
    how `topOf` behaves. -/
theorem the_top_of_the_index_range_is_its_bound_at_the_stated_bounds :
    (topOf (R 1) == 1 && topOf (R 2) == 2 && topOf (R 3) == 3 && topOf (R 4) == 4) = true := by
  decide

end B304

-- The polarity controls print FIRST, as they appear first in the file.
#print axioms B304.below_top_range_is_nonempty_from_two_up
#print axioms B304.index_range_grows_with_its_bound
#print axioms B304.the_two_ranges_have_the_lengths_their_bounds_name
#print axioms B304.top_of_reports_the_largest_entry
#print axioms B304.both_ranges_are_empty_at_zero
#print axioms B304.index_range_at_bound_one_is_a_single_point
#print axioms B304.below_top_range_at_bound_one_is_empty
#print axioms B304.the_single_point_at_bound_one_is_the_top_and_the_top_is_the_bound
#print axioms B304.the_top_of_the_index_range_is_its_bound_at_the_stated_bounds
