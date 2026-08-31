/-
  b271 · AbsorptionFunctionalShadow.lean — THE VANILLA LEG (zero axioms)
  ======================================================================

  The two-leg ruling (Rule 5) governs: VANILLA leg — vanilla Lean 4, `decide` only,
  expected profile per terminal: "does not depend on any axioms".

  WHAT THIS MODULE COMPILES — and, far more importantly, WHAT IT DOES NOT.

  IT COMPILES NOTHING ABOUT `E₁`. The act's one genuinely new mathematical step is that
  `g := 4q·P₁e₀` satisfies `S g = q g`, and THAT IS NOT FINITE-DECIDABLE HERE: it rests on
  the character sum `Σ_{m'} ζ_N^{m m'} = N·[m ≡ 0]`, i.e. on cyclotomic arithmetic. A toy
  model of it with integer stand-ins WOULD COMPILE CLEANLY AND SETTLE NOTHING, in a file
  whose header named the real operator — b269's species, and the test was applied again
  here and answered by LEAVING THAT STEP OUT. It is derived and exactly controlled in
  relay `data/b271_top_level_no_go.txt` and `data/b271_run.txt`, and nowhere below.

  IT COMPILES NO BARRIER. The act's verdict is (ESCAPE) — there is no no-go about `E₁` to
  shadow, and a file that suggested one would be worse than no file.

  IT COMPILES NO AGGREGATION AND ADOPTS NO CANDIDATE. M-2 is owed and stays owed.

  WHAT IS HERE is the one decidable thing b270's `BallAbsorptionShadow` does NOT already
  hold. That file compiles the INDEX law — `pⁿ·m` always lands in the ball. This file
  compiles the FUNCTIONAL consequence AND, more to the point, ITS CONVERSE POLARITY:

    (1) FOR A BALL-VANISHING `g`, the functional `Σ_m f m · g (pⁿ·m mod N)` is `0`, and it
        is `0` FOR TWO DIFFERENT `f` — because the lemma places NO hypothesis on `f` at
        all, and a single `f` would leave that indistinguishable from luck.

    (2) FOR A `g` THAT DOES NOT VANISH ON THE BALL, the same functional with the same `f`
        is NONZERO. WITHOUT THIS PART (1) WOULD BE COMPATIBLE WITH A FUNCTIONAL THAT IS
        IDENTICALLY ZERO and would settle nothing — the not-dead witness, exactly as
        b270's `hasLiveStep` was.

  SO WHAT (1)+(2) TOGETHER COMPILE IS: BALL-VANISHING IS LOAD-BEARING IN THE LEMMA, NOT
  DECORATIVE. That is the whole claim, and it is the whole of what may be read off.

  The `g` of part (2) has the SHAPE of the act's witness at (p,n) = (3,1) — `2q + 2 = 8`
  at `0` and `2` elsewhere, `q = 3`. THAT IT HAS THAT SHAPE IS NOT EVIDENCE THAT THE
  WITNESS IS IN `E₁`; the shape is carried so the polarity control is the act's own object
  rather than an arbitrary one, and nothing more is claimed for it.

  A NOTE ON THE ENCODING, because it changed to keep the profile honest. The vectors are
  FUNCTIONS `Nat → Int`, not lists. A first draft indexed lists with `List.getD`, and that
  route pulls in `propext`: six of seven terminals then printed "depends on axioms:
  [propext]" UNDER A HEADER PROMISING ZERO. The header was not weakened to match — the
  ENCODING was changed until the printed profile matched the header.

  WHAT IS NOT DECIDED HERE, AND MUST NOT BE READ INTO IT:
    · that `g` lies in `E₁` — cyclotomic, relay's, deliberately absent;
    · that (SPEC-1) is satisfiable — that conclusion needs the `E₁` step;
    · anything about `Son`, the complete roster, or `h2`.
-/

namespace B271

/-- The cell: `p = 3`, `n = 1`, so `N = p^(2n) = 9` and the ball is the multiples of `3`. -/
def N : Nat := 9
def pn : Nat := 3

def inBall (m : Nat) : Bool := m % pn == 0

/-- The functional of the lemma: `Σ_{m < N} f m · g (pⁿ·m mod N)`.
    NOTE THE SHAPE — `f` is summed against `g` EVALUATED AT THE ABSORBED INDEX, and NO
    HYPOTHESIS IS PLACED ON `f` ANYWHERE, here or in the derivation this shadows. -/
def functional (f g : Nat → Int) : Int :=
  (List.range N).foldl (fun acc m => acc + f m * g ((pn * m) % N)) 0

/-- Does `v` vanish at every ball index below `N`? -/
def vanishesOnBall (v : Nat → Int) : Bool :=
  (List.range N).all (fun m => (!inBall m) || (v m == 0))

/-- A `g` that VANISHES on the ball `{0,3,6}` and is arbitrary elsewhere. -/
def gVan (m : Nat) : Int := if m % 3 == 0 then 0 else (m : Int)

/-- A `g` with the act's witness shape at `q = 3`: `2q + 2 = 8` at `0`, `2` elsewhere.
    IT DOES NOT VANISH ON THE BALL. -/
def gWit (m : Nat) : Int := if m == 0 then 8 else 2

/-- Two DIFFERENT `f`, one of them taking negative values, because the lemma constrains
    `f` not at all and a single well-behaved `f` would not show that. -/
def fOnes (_ : Nat) : Int := 1
def fWild (m : Nat) : Int := if m % 2 == 0 then (m : Int) + 3 else -((m : Int) * 2 + 1)

/-! ### (1) THE LEMMA'S POSITIVE SIDE: a ball-vanishing `g` kills the functional,
    for two unrelated `f`. -/

theorem van_ones : functional fOnes gVan = 0 := by decide
theorem van_wild : functional fWild gVan = 0 := by decide

/-- And the hypothesis really is satisfied by `gVan` — decided, not assumed. -/
theorem gVan_vanishes : vanishesOnBall gVan = true := by decide

/-! ### (2) THE NOT-DEAD WITNESS AND THE POLARITY REFUSALS, WHICH HERE ARE THE SAME
    THEOREMS: each is a TRUE statement asserting a NEGATIVE. Drop the lemma's hypothesis
    and the functional STOPS vanishing, with the SAME `f` — which is what makes (1) a
    lemma rather than a triviality. -/

theorem wit_ones_ne : functional fOnes gWit ≠ 0 := by decide
theorem wit_wild_ne : functional fWild gWit ≠ 0 := by decide

/-- And `gWit` genuinely fails the hypothesis, so (2) is not testing a different thing. -/
theorem gWit_not_vanishes : vanishesOnBall gWit = false := by decide

/-- The absorbed index never escapes the ball — b270's law, RE-DECIDED HERE ONLY BECAUSE
    THIS FILE'S FUNCTIONAL DEPENDS ON IT, and NOT as a new finding. -/
theorem absorbed_indices_in_ball :
    (List.range N).all (fun m => inBall ((pn * m) % N)) = true := by decide

/-! ### THE AXIOM PROFILE, PRINTED BY THIS FILE ITSELF.

    b227's standard: a claimed compile is reported ONLY from its printed profile. These
    prints live in the banked file so the profile is produced by compiling the artefact
    that was banked — not by compiling a copy of it. -/

#print axioms B271.van_ones
#print axioms B271.van_wild
#print axioms B271.gVan_vanishes
#print axioms B271.wit_ones_ne
#print axioms B271.wit_wild_ne
#print axioms B271.gWit_not_vanishes
#print axioms B271.absorbed_indices_in_ball

end B271
