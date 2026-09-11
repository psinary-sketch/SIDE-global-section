/-
  # b414 — THE PREDICATE NAMED, AND THE GENERAL CLAUSE STATED WITHOUT ITS PROOF.

  Lean 4 (v4.29.1, pinned), no Mathlib import, `decide` and `rfl` only; the axiom
  profile is PRINTED, never assumed. Expected profile for every terminal here:
  "does not depend on any axioms".

  ## WHAT THIS MODULE IS FOR.

  `B329.finite_side_silence` states three conjuncts under the hypothesis `2 ≤ p`.
  Conjuncts (a) and (b) are GENERAL and are proved for every `p ≥ 2`. Conjunct (c)
  — the compact part's smear vanishing — is GUARDED BY A SEVEN-ELEMENT LIST and is
  discharged by `decide`, seven times. THE HYPOTHESIS `2 ≤ p` NEVER BITES ON (c),
  because the guard admits only the seven cells whatever `p` is.

  So the obvious generalisation — drop the guard and keep `2 ≤ p` — was never
  tested. b413 tested it OUTSIDE the kernel, on these definitions transcribed into
  Python, with the seven decided cells reproduced as a positive control. IT IS
  FALSE. This module re-runs that test INSIDE the kernel, on `B329`'s own
  `ballQ`, `sumAN` and `sumAQ`, so the refutation is the kernel's and not a
  transcription's, and NAMES THE CONDITION THAT ACTUALLY SEPARATES the bases where
  the identity holds from the bases where it fails.

  ## THE CONDITION IS NOT PRIMALITY.

  `FiniteSideSeal.lean`'s own header says, at (T1.4), that a residue `p` does not
  divide is a unit of `Z/p^k` *exactly when `p` is prime*, and that this
  identification is the library's and IS NOT COMPILED HERE. The file therefore
  named the missing identification in advance — AND NAMED THE WRONG CONDITION FOR
  IT. The identity holds at `4`, `8`, `9`, `16`, `25`, `27`, `32` and `49`, every
  one of them composite. A hypothesis of primality would be SOUND and would throw
  away every proper prime power at which the statement is true.

  THE CONDITION IS A SINGLE DISTINCT PRIME FACTOR — exactly when `B329.units`'
  filter `u % p != 0` picks out the actual unit group of the grid. It is stated
  here as `singlePrimeFactor`, compiled and decidable, so that the open statement
  below has an exact subject rather than a prose one.

  WHY THE CAVEAT SURVIVED. The seal's seven decided cells have bases `2, 3, 5, 7`.
  EVERY ONE OF THEM IS PRIME, so the caveat is exactly right on the set the kernel
  decides and wrong only on the set it does not. It could never have been caught
  by re-reading the decided cells — only by leaving them.

  ## THE NAMED OPEN STATEMENT (correspondence row; never a sorry).

  For every base `p` with `singlePrimeFactor p = true` and every level `n`,
      `ballQ p n * sumAN p n = sumAQ p n`.

  THIS IS NOT PROVED HERE AND NOTHING BELOW SHOULD BE READ AS PROVING IT. It is a
  NAMED OPEN STATEMENT in the sense the kernel already uses in `KLSilence`,
  `PairingShadow`, `PlancherelShadow` and `CrossPlaceShadow`: recorded in this
  docstring and in the CORRESPONDENCE row, carried by NO `sorry` and by NO
  `Prop`-valued definition standing in for a result. `Core/` contains zero
  occurrences of `sorry` and this module adds none.

  What IS compiled below is: the predicate; that all seven decided cells satisfy
  it; that the naive generalisation over `2 ≤ p` is FALSE, with witnesses; and
  that primality is not the separator, with witnesses on the other polarity. A
  quantifier is proposed here only together with what refutes the loose one.

  WHAT THIS MODULE DOES NOT DO. It does not touch `FiniteSideSeal.lean`. It does
  not restate, rename or supersede `compact_smear_vanishes_at_cells` — the seven
  cells survive as the instances they are, and would be corollaries of the open
  statement if anyone proves it. It discharges no premise, moves no grade, restates
  no door, and says nothing about `h2`. It does not decide `M-2`.

  ## THE COST OF DECIDING, AND WHY THE LISTS BELOW STOP WHERE THEY STOP.

  There are TWO KINDS OF LIST below and they have different reaches.

  The lists that decide only `singlePrimeFactor` or `isPrime` cost trial division
  and reach EVERY ONE of b413's eighteen bases — all ten counterexamples and all
  eight holding prime powers. THE CLASSIFICATION IS CERTIFIED IN FULL HERE.

  The lists that decide `compactSmearHolds` are kernel reduction over
  `List.range (p ^ (2 * n))` twice nested, costing about `(p^2 - p) * p^2` at
  level one. THE FRONTIER WAS MEASURED, NOT GUESSED: base `10` decides in seconds
  and base `12` ran 292 seconds at `maxRecDepth 2000000` and `maxHeartbeats
  1000000` and did not land. The cliff is not proportional — 2.1× the work cost
  more than 28× the time — so it cannot be predicted from a work count and has to
  be measured. Bases past it remain b413's measurement, cited to relay
  `data/b413_extract.txt` and `data/b414_ladder.txt`.

  AN AFFORDABILITY LIMIT IS A PROPERTY OF KERNEL REDUCTION, NOT A RESULT ABOUT THE
  ARITHMETIC. This kernel not deciding `26` says nothing whatever about `26`;
  b413 decided it in Python in milliseconds. The two are not run together here.

  AND THE DEFAULT RECURSION DEPTH IS A TRAP RATHER THAN A LIMIT: a `decide` that
  runs out does not fail cleanly, it yields a terminal carrying `sorryAx` while
  the build prints an error. Measured at this act's scratch probe — three of four
  terminals compiled to `sorryAx` and the fourth was clean, and ONLY THE PRINTED
  PROFILE DISTINGUISHED THEM. A green build is not evidence; the profile is.

  Bank: relay `data/b414_the_predicate_named.txt`.
  Registration: relay `data/b414_registration_2026-09-10.txt`, sealed before any
  of this existed.
-/
import FiniteSideSeal

set_option maxRecDepth 2000000

namespace SinglePrimeFactor

/-- "`d` is prime", by trial division below `d`, as a `Bool`. Written without
    `Nat.Prime`, whose lemmas carry `propext`, and without any import from outside
    the axiom-free set. THE ONE PRIMITIVE THIS MODULE ADDS TO `Core/`: a primality
    notion, which `Core/` did not previously contain in any form. -/
def isPrime (d : Nat) : Bool :=
  d != 0 && d != 1 && (List.range d).all (fun k => k == 0 || k == 1 || d % k != 0)

/-- The distinct prime divisors of `m`, listed below `m + 1`. -/
def primeDivisors (m : Nat) : List Nat :=
  (List.range (m + 1)).filter (fun d => isPrime d && m % d == 0)

/-- THE PREDICATE. `m` has exactly one distinct prime factor — equivalently, `m`
    is a power of a single prime with positive exponent. This is the hypothesis
    the general form of `B329.finite_side_silence`'s conjunct (c) needs. -/
def singlePrimeFactor (m : Nat) : Bool := (primeDivisors m).length == 1

/-- Conjunct (c)'s identity at one cell, as a `Bool`, on `B329`'s own definitions
    and not on a restatement of them. -/
def compactSmearHolds (p n : Nat) : Bool :=
  B329.ballQ p n * B329.sumAN p n == B329.sumAQ p n

/-! ### (1) THE PREDICATE'S OWN FIXTURES, IN BOTH POLARITIES. -/

/-- `isPrime` decides correctly at the degenerate arguments and at the smallest
    prime, the smallest composite and a prime square. A predicate whose fixtures
    run in one polarity only is not tested. -/
theorem isPrime_fixtures :
    (isPrime 0, isPrime 1, isPrime 2, isPrime 3, isPrime 4, isPrime 9, isPrime 49)
      = (false, false, true, true, false, false, false) := by decide

/-- `singlePrimeFactor` admits prime powers and refuses everything else, including
    both degenerate arguments. `0` and `1` have no prime factors and are refused. -/
theorem singlePrimeFactor_fixtures :
    (singlePrimeFactor 0, singlePrimeFactor 1, singlePrimeFactor 2,
     singlePrimeFactor 4, singlePrimeFactor 6, singlePrimeFactor 49)
      = (false, false, true, true, false, true) := by decide

/-! ### (2) THE SEVEN DECIDED CELLS ARE INSTANCES OF THE OPEN STATEMENT. -/

/-- Every cell `B329.cells` decides satisfies the predicate. So the open statement,
    IF ANYONE PROVES IT, subsumes `B329.compact_smear_vanishes_at_cells` rather
    than competing with it — and this act does not prove it. -/
theorem cells_all_single_prime_factor :
    B329.cells.all (fun c => singlePrimeFactor c.1) = true := by decide

/-- And the identity does hold at all seven, recomputed here from `B329`'s own
    definitions. THE POSITIVE CONTROL: a re-run that failed to reproduce what the
    kernel already decides would be measuring itself. -/
theorem cells_all_hold :
    B329.cells.all (fun c => compactSmearHolds c.1 c.2) = true := by decide

/-! ### (3) THE NAIVE GENERALISATION OVER `2 ≤ p` IS FALSE, WITH WITNESSES. -/

/-- The smallest base with two distinct prime factors, and the identity fails
    there. `6 ≥ 2`, so THIS IS A COUNTEREXAMPLE TO THE STATEMENT OBTAINED BY
    DROPPING CONJUNCT (c)'S GUARD AND KEEPING THE SEAL'S OWN HYPOTHESIS. -/
theorem base_six_breaks_the_identity :
    (2 ≤ 6) ∧ compactSmearHolds 6 1 = false := by decide

/-- The values themselves, so the failure is a magnitude and not only a bit. -/
theorem base_six_values :
    B329.ballQ 6 1 * B329.sumAN 6 1 = 468 ∧ B329.sumAQ 6 1 = 324 := by decide

/-- Further witnesses on the failing side, every one of them `≥ 2` and every one
    of them refused by the predicate. -/
theorem two_prime_bases_break_the_identity :
    ([6, 10].all (fun p => compactSmearHolds p 1 == false)) = true := by decide

/-- And the predicate refuses exactly those. -/
theorem two_prime_bases_are_refused :
    ([6, 10, 12, 14, 15, 18, 20, 21, 22, 26].all (fun p => singlePrimeFactor p == false)) = true := by decide

/-! ### (4) AND PRIMALITY IS NOT THE SEPARATOR, WITH WITNESSES ON THE OTHER SIDE. -/

/-- Witnesses on the holding side that are COMPOSITE. A hypothesis of primality —
    which is what `FiniteSideSeal.lean`'s own (T1.4) names — would be sound and
    would discard every one of these. -/
theorem composite_bases_keep_the_identity :
    ([4, 8, 9].all (fun p => compactSmearHolds p 1)) = true := by decide

/-- Each of them is composite, so the previous theorem is not vacuous. -/
theorem those_bases_are_composite :
    ([4, 8, 9, 16, 25, 27, 32, 49].all (fun p => isPrime p == false)) = true := by decide

/-- And the predicate admits them. This is the pair that separates the two
    candidate conditions: COMPOSITE, AND ADMITTED, AND THE IDENTITY HOLDS. -/
theorem those_bases_are_admitted :
    ([4, 8, 9, 16, 25, 27, 32, 49].all (fun p => singlePrimeFactor p)) = true := by decide

/-! ### (5) THE PREDICATE AGREES WITH THE IDENTITY ON EVERY BASE DECIDED HERE. -/

/-- The decided range at level one, both polarities in one statement: the identity
    holds at a base exactly when the predicate admits it. THIS IS THE EVIDENCE FOR
    THE OPEN STATEMENT AND IT IS NOT A PROOF OF IT — a finite check over a list
    decides nothing about the bases not in the list.

    SPLIT INTO THREE BECAUSE OF A MEASURED CLIFF, NOT FOR TIDINESS. Kernel
    reduction here costs about `(p^2 - p) * p^2` at a base, and the frontier on
    this machine sits between `10` (decides in seconds) and `12` (ran 292s and did
    not land). A single `decide` over all nine bases exceeds that frontier even
    though every base in it is individually under. -/
theorem predicate_agrees_at_small_bases :
    ([2, 3, 4, 5, 6, 7].all
      (fun p => compactSmearHolds p 1 == singlePrimeFactor p)) = true := by decide

/-- The same agreement at the two next bases, one a prime power and one prime. -/
theorem predicate_agrees_at_eight_and_nine :
    ([8, 9].all (fun p => compactSmearHolds p 1 == singlePrimeFactor p)) = true := by decide

/-- And at the largest base this kernel affords. -/
theorem predicate_agrees_at_ten :
    ([10].all (fun p => compactSmearHolds p 1 == singlePrimeFactor p)) = true := by decide

/-- At level two, over the bases level two can afford, the agreement survives —
    evidence that the condition is on the base alone and not on the pair. -/
theorem predicate_agrees_at_level_two :
    ([2, 3].all (fun p => compactSmearHolds p 2 == singlePrimeFactor p)) = true := by
  decide

end SinglePrimeFactor
