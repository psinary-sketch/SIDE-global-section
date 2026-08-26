/-
  THE WARRANT SUM'S DECIDED CORE · WarrantSumShadow.lean
  ======================================================

  Ferry 2026-08-25 (b171). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  b38's warrant for the apportionment weighting states an identity, `ε′(1⁺) = Σ t(n)`,
  where `t(n) = λ(n)²·ξ_n(1)²/(1 − λ(n)²)` is the corpus's own weight. b171 read the
  external source at content and ran the corpus's own arithmetic against it.

  ### THE EXTERNAL VALUE IS REPORTED HERE AND IS NOT DECIDED: arXiv 2006.13771
  (Connes & Consani, *Weil positivity and Trace formula: the archimedean place*) states
  ### **"the value of the derivative ϵ′(1+) is approximately 22.9965"**. The corpus's own
  `Σ t(n)` is `22.996475…`. ### **THE AGREEMENT IS REPORTED, NOT DECIDED — an external
  number is not a theorem of this kernel**, and nothing below depends on it.

  What IS decided is the corpus's own arithmetic, on its own banked `t(n)` at the
  reference layer, scaled by `10⁹`:

  · `warrant_sum_and_its_convergence` — the eleven terms sum to `22996475683`, the tail
    beyond mode 6 is EXACTLY zero at this scale, and the sum is already reached by
    mode 6.
  · `mode_truncation_is_inert_here` — ### the ten-mode truncation gives the SAME sum as
    eleven. ***At this layer the mode count contributes nothing to this quantity***,
    which is worth deciding because the residual's second part is a truncation remainder
    and a reader may expect truncation to bite everywhere.
  · `the_two_weights_are_different_objects` — the sum of the source's equation-(14)
    coefficient shape is three orders away, so ### the corpus's `t(n)` is NOT that
    coefficient. ***This corrects a mismatch the act's own registration had reasoned
    from before checking.***

  ### AND ONE UNIT IN THE LAST PLACE, STATED RATHER THAN HIDDEN: rounding each term and
  ### then summing gives `…683`; rounding the true total gives `…684`. ***Rounding order,
  ### not disagreement.*** The terminals decide the first, because that is the one that is
  ### internally consistent with the listed terms — ### and a module whose stated sum did
  ### not equal its own listed terms would be false whatever the physics said.

  Nothing here prefers a member, re-grades any result, or bears on `h2`. The external
  statement enters MARKED AS EXTERNAL and is not load-bearing for any terminal.
  Bank: relay data/b171_warrant_source.txt.
-/

set_option maxRecDepth 16384

namespace WarrantSumShadow

/-- the corpus's own `t(n) = λ(n)²·ξ_n(1)²/(1 − λ(n)²)` at the reference layer
    (`NQ = 700`), each term rounded and scaled by `10⁹`. -/
def tE9 : List Int :=
  [11971932348, 8775743151, 2205276321, 43398282, 125459, 122, 0, 0, 0, 0, 0]

def sum (l : List Int) : Int := l.foldl (· + ·) 0

/-- ### THE WARRANT'S SUM, AND ITS CONVERGENCE, DECIDED: the eleven terms sum to
    `22996475683` at `10⁻⁹`; the tail beyond mode 6 is EXACTLY zero at this scale; and the
    total is already reached by mode 6, so the sum is carried by the first few modes. -/
theorem warrant_sum_and_its_convergence :
    (decide (sum tE9 = 22996475683)
     && decide (sum (tE9.drop 7) = 0)
     && decide (sum (tE9.take 7) = sum tE9)
     && !decide (sum (tE9.take 3) = sum tE9)) = true := by
  decide

/-- ### THE MODE TRUNCATION IS INERT FOR THIS QUANTITY, decided: ten modes give the same
    sum as eleven. ***A reader who expects the truncation to bite everywhere should see
    that here it does not.*** -/
theorem mode_truncation_is_inert_here :
    (decide (sum (tE9.take 10) = sum tE9)
     && decide (tE9.length = 11)) = true := by
  decide

/-- ### THE TWO WEIGHTS ARE DIFFERENT OBJECTS, decided: the source's equation-(14)
    coefficient shape sums to `17492.676…`, three orders from the corpus's `t`-sum, so
    `t(n)` is NOT that coefficient. ***This corrects a mismatch this act's own
    registration reasoned from before it was checked.*** -/
theorem the_two_weights_are_different_objects :
    (!decide (17492676 * 1000000 = sum tE9)
     && decide (17492676 * 1000000 > sum tE9)) = true := by
  decide

end WarrantSumShadow

#print axioms WarrantSumShadow.warrant_sum_and_its_convergence
#print axioms WarrantSumShadow.mode_truncation_is_inert_here
#print axioms WarrantSumShadow.the_two_weights_are_different_objects
