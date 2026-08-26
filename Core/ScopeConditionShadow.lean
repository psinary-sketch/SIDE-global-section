/-
  THE SCOPE CONDITION'S DECIDED CORE · ScopeConditionShadow.lean
  ==============================================================

  Ferry 2026-08-25 (b173). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  The external source (Connes–Consani, `2006.13771`) carries two statements the corpus
  cites. ### **Lemma 5.4 has NO interval hypothesis** — it states
  `ε′(1⁺) = Σ λ(n)²/(1−λ(n)²)·ξ_n(1)²`, which is the corpus's own `t(n)` weighting.
  ### **Proposition 5.5 DOES**: *"Let `I ⊂ [−log 2, log 2]` be an interval of length
  `≤ log 2`"*, and that hypothesis is load-bearing in its own proof.

  ### **THE CORPUS'S LOAD-BEARING USE IS LEMMA 5.4's IDENTITY, SO THE HYPOTHESIS DOES NOT
  ### REACH IT — that is the act's verdict and it is NOT what this module decides.**

  What this module decides is ### **THE HAZARD**, which is worth deciding precisely
  because the verdict is SATISFIED: the corpus's own interval is `[−2L, 2L]` in
  `u = log ρ` with `2L = log(a²)` (b36, R1's `u`-grid on `[−2L, 2L]` and R2's
  `ρ_max = a²` with its registered symmetric extension). ### **Compared against
  Proposition 5.5's hypothesis, at every recorded cell:**

  · `containment_holds_only_at_the_smallest_cell` — `I ⊂ [−log 2, log 2]` requires
    `2L ≤ log 2`, which holds at `a² = 2` and ### **at no other recorded cell.**
  · `the_length_bound_fails_at_every_cell` — the length is `4L`, and `4L ≤ log 2`
    ### **fails everywhere, including at the smallest cell, where it fails by exactly a
    factor of two.**
  · `the_smallest_cell_sits_exactly_on_the_containment_edge` — at `a² = 2`,
    `2L = log 2` to the decided precision, so containment holds only as a boundary case.

  ### **SO ANY FUTURE USE OF PROPOSITION 5.5's OPERATOR STATEMENT WOULD BE OUTSIDE ITS
  ### HYPOTHESIS AT EVERY RECORDED CELL.** ***That is a hazard filed, not a defect found:
  the corpus does not presently make that use.***

  Values scaled by `10⁶`; `log 2 = 693147`. Nothing here prefers a member, re-grades any
  result, or bears on `h2`. Bank: relay data/b173_scope_condition.txt.
-/

set_option maxRecDepth 16384

namespace ScopeConditionShadow

/-- `log 2`, scaled by `10⁶` — Proposition 5.5's bound. -/
def log2E6 : Int := 693147

/-- `2L = log(a²)` at the recorded cells `a² ∈ {2,3,4,8,9,12,16,24,48}`, scaled by `10⁶`.
    The corpus's interval is `[−2L, 2L]`, so its LENGTH is `4L`. -/
def twoLE6 : List Int :=
  [693147, 1098612, 1386294, 2079442, 2197225, 2484907, 2772589, 3178054, 3871201]

/-- ### CONTAINMENT `I ⊂ [−log 2, log 2]` HOLDS AT THE SMALLEST CELL AND NOWHERE ELSE,
    decided: `2L ≤ log 2` at `a² = 2`, and `2L > log 2` at all eight others. -/
theorem containment_holds_only_at_the_smallest_cell :
    (decide ((twoLE6.take 1).all (fun v => decide (v ≤ log2E6)))
     && decide ((twoLE6.drop 1).all (fun v => decide (v > log2E6)))
     && decide (twoLE6.length = 9)) = true := by
  decide

/-- ### THE LENGTH BOUND FAILS AT EVERY RECORDED CELL, decided: the interval's length is
    `4L`, and `4L > log 2` everywhere — ### including at the smallest cell, where it
    exceeds the bound by exactly a factor of two. -/
theorem the_length_bound_fails_at_every_cell :
    (twoLE6.all (fun v => decide (2 * v > log2E6))
     && decide (2 * (twoLE6.take 1).foldl (· + ·) 0 = 2 * log2E6)) = true := by
  decide

/-- ### THE SMALLEST CELL SITS EXACTLY ON THE CONTAINMENT EDGE: `2L = log 2` at `a² = 2`
    to the decided precision, so containment there is a boundary case and not slack. -/
theorem the_smallest_cell_sits_exactly_on_the_containment_edge :
    (decide (twoLE6.head? = some log2E6)
     && decide (twoLE6.getLast? = some 3871201)
     && decide (3871201 > 5 * log2E6)) = true := by
  decide

end ScopeConditionShadow

#print axioms ScopeConditionShadow.containment_holds_only_at_the_smallest_cell
#print axioms ScopeConditionShadow.the_length_bound_fails_at_every_cell
#print axioms ScopeConditionShadow.the_smallest_cell_sits_exactly_on_the_containment_edge
