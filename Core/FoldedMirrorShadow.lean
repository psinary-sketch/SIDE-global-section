/-
  THE TWO — THE FOLDED MIRROR TERM, AND WHAT IT DOES NOT SETTLE
  · FoldedMirrorShadow.lean
  =============================================================

  Ferry 2026-08-28 (b231, THE TWO). Vanilla Lean 4 (v4.29.1 pinned), no
  imports; the axiom profile is PRINTED, never assumed.

  ### WHAT THIS FILE IS THE SHADOW OF.
  b229 adopted the ledger's prime side as a stated definition,

      `wPrimes(a) := Σ_p Σ_{k=1}^{n_p(a)} (2 log p / p^{k/2}) · corr(log p^k)`,

  and recorded that the constant `2` is carried by no owner's explanation.
  b231 tests one reading of it: that the `2` is a ### **FOLDED MIRROR TERM** —
  the `k < 0` half of a two-ended sum laid onto the `k > 0` half, which is
  licensed exactly when the summand is EVEN in the signed index.

  ### THE TWO FINITE-DECIDABLE PARTS, AND THEY ARE ALL THIS FILE CLAIMS:

    (1) ### **THE EVENNESS**, and the distinction it rests on. The instrument
        writes `corr = np.convolve(w, w)` — a ### **CONVOLUTION**, not a
        correlation. For a general signal these are DIFFERENT objects and the
        convolution need not be even. ### **THEY COINCIDE, AND THE RESULT IS
        EVEN, PRECISELY BECAUSE THE BUMP IS EVEN.** Both halves are witnessed
        here, and the NON-even witness is what gives the even one content.

    (2) ### **THE FOLD** — for a summand even in the signed index, the
        two-ended sum over a finite index list equals the one-sided sum
        DOUBLED. With a second witness that ### **IT FAILS WITHOUT EVENNESS.**

  ### WHY THE SUMMAND, NOT THE PAIRING, CARRIES THE EVENNESS HERE.
  The weight is absorbed into the term `T k`. That is the faithful shape: in a
  two-ended prime sum the summand is `Λ(n)·n^(−1/2)·g(±log n)`, whose weight
  depends on `n` and therefore on `|k|`, so the whole summand — not the pairing
  alone — is what must be even for the halves to coincide.

  ### WHAT THIS FILE DOES NOT SAY, AT FULL PROMINENCE.
  ### **IT DOES NOT SAY THAT THE CORPUS'S PRIME SIDE *IS* THE TWO-ENDED SUM.**
  Nothing here can say that. b231's search found ### **NO OWNER ANYWHERE IN THE
  FOUR TREES WHO WRITES THE TWO-ENDED SUM** `Σ_n Λ(n) n^(−1/2) [g(log n) +
  g(−log n)]`, in any notation. The fold is an identity; the claim that the
  adopted formula AROSE by folding it is ### **AN IMPORT FROM OUTSIDE THE
  CORPUS**, and it is listed as one. ### **THIS FILE COMPILES THE ALGEBRA, NOT
  THE PROVENANCE.**

  ### AND IT TOUCHES NO LEFT-SIDE OBJECT. b229's standing clause governs: the
  adopted target may never define, calibrate, or tune the left side. There is
  no left side in this file at all.

  ### TWO REPAIRS THE PRINTS FORCED, RECORDED BECAUSE THEY ARE REUSABLE.
  A first draft of this file compiled clean and printed ### **EIGHT
  AXIOM-BEARING TERMINALS** against Core's bar of 390 axiom-free lines. The
  profile convicted it, exactly as at b227. The two causes, both now avoided:

    · ### **AN OVERLAPPING PATTERN IN `conv`** (a `[x]` case beside `x :: xs`)
      compiles to a match whose `rfl` proofs drag `propext`. ### The structural
      two-case definition below needs no such case — `addS` already pads — and
      every `rfl` over it is axiom-free.
    · ### **CORE'S `Int` ALGEBRA LEMMAS ARE NOT AXIOM-FREE.** `Int.mul_add`,
      `Int.add_assoc` and `Int.add_left_comm` each print `[propext]`, and
      `omega` prints `[propext, Quot.sound]`. ### **THE `Nat` LEMMAS ARE CLEAN.**
      So the fold carries its values in `Nat` and its index in `Int` — the
      mirror `-k` stays visible, and the arithmetic stays inside the bar.
      ### **CORE'S "ZERO-AXIOM BAR" IS, IN PRACTICE, A `Nat` BAR.**
-/

namespace FoldedMirrorShadow

/-! ### PART A — THE CONTROLS FIRST, AS THE FERRY ORDERS.

    A signal is a finite list of integer samples; "even" is palindromy, the
    discrete form of symmetry about the centre. Decidable negatives are stated
    at `Bool` and closed by `rfl`: ### `decide` on list equality would import
    `propext` and break the bar. -/

abbrev Signal := List Int

def smul (c : Int) : Signal → Signal
  | [] => []
  | x :: xs => c * x :: smul c xs

def addS : Signal → Signal → Signal
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addS xs ys

/-- Full discrete convolution, the instrument's `np.convolve(·, ·, "full")`.
    ### Structural in the first argument; `addS` pads, so no length case. -/
def conv : Signal → Signal → Signal
  | [], _ => []
  | x :: xs, ys => addS (smul x ys) (0 :: conv xs ys)

/-- The autocorrelation — the object `corr` is NAMED after. -/
def corr (w : Signal) : Signal := conv w w.reverse

/-- An even (palindromic) signal — the bump's shape. -/
def wEven : Signal := [1, 2, 5, 2, 1]

/-- ### THE POLARITY CONTROL: a signal that is NOT even. -/
def wOdd : Signal := [1, 2, 5, 1, 0]

theorem even_signal_is_palindromic : wEven.reverse = wEven := rfl

/-- ### THE CONTROL IS A REAL CONTROL: this signal genuinely fails evenness. -/
theorem odd_signal_is_not_palindromic : (wOdd.reverse == wOdd) = false := rfl

/-! ### PART B — CONVOLUTION IS NOT CORRELATION, AND EVENNESS IS WHAT JOINS THEM. -/

/-- For an even signal the self-convolution is even. -/
theorem conv_even_of_even : (conv wEven wEven).reverse = conv wEven wEven := rfl

/-- ### THE WITNESS THAT MAKES THE ABOVE NON-VACUOUS: without evenness it FAILS. -/
theorem conv_not_even_witness :
    ((conv wOdd wOdd).reverse == conv wOdd wOdd) = false := rfl

/-- The autocorrelation is even for the even signal. -/
theorem autocorr_even_of_even : (corr wEven).reverse = corr wEven := rfl

/-- ### AND THE AUTOCORRELATION IS EVEN EVEN WHEN THE SIGNAL IS NOT — evenness of
    `corr` is a property of the CORRELATION, not of the signal. ### THIS PAIR OF
    FACTS IS WHAT LOCATES THE INSTRUMENT'S RISK. -/
theorem autocorr_even_even_when_signal_is_not : (corr wOdd).reverse = corr wOdd := rfl

/-- For an even signal, what the instrument WRITES equals what it is CALLED. -/
theorem conv_eq_corr_of_even : conv wEven wEven = corr wEven := rfl

/-- ### THE FINDING THAT LANDS ON b229's OWN ADOPTION SENTENCE: for a signal that
    is not even, `convolve(w, w)` is ### **NOT** the autocorrelation. b229 wrote
    "corr IS THE AUTOCORRELATION OF THE BUMP". ### **IT IS — BUT ONLY BECAUSE THE
    BUMP IS EVEN, WHICH b229 NEVER CHECKED.** -/
theorem conv_ne_corr_witness : ((conv wOdd wOdd) == corr wOdd) = false := rfl

/-! ### PART C — THE FOLD. The general identity, proved by induction in term
    mode, plus both polarity controls. -/

/-- Evenness of the summand in the signed index. -/
def IsEvenFn (T : Int → Nat) : Prop := ∀ x, T (-x) = T x

/-- The two-ended sum: each index contributes its term AND its mirror. -/
def twoEnded (T : Int → Nat) : List Int → Nat
  | [] => 0
  | k :: ks => (T k + T (-k)) + twoEnded T ks

/-- The one-sided sum — the shape of the adopted `wPrimes`, whose `k` runs from
    `1` upward and never below. -/
def oneSided (T : Int → Nat) : List Int → Nat
  | [] => 0
  | k :: ks => T k + oneSided T ks

/-- ### THE FOLD, IN ONE LINE: for a summand even in the signed index, the
    two-ended sum is exactly the one-sided sum DOUBLED — which is the `2`.
    ### **THIS IS THE WHOLE ALGEBRAIC CONTENT OF THE READING**, and it is free:
    it imports nothing and assumes nothing about primes, logs or weights. -/
theorem two_ended_eq_two_times_one_sided (T : Int → Nat) (h : IsEvenFn T) :
    ∀ S : List Int, twoEnded T S = oneSided T S + oneSided T S
  | [] => rfl
  | k :: ks => by
      show (T k + T (-k)) + twoEnded T ks
           = (T k + oneSided T ks) + (T k + oneSided T ks)
      rw [h k, two_ended_eq_two_times_one_sided T h ks]
      rw [Nat.add_assoc, Nat.add_assoc]
      rw [Nat.add_left_comm (oneSided T ks) (T k) (oneSided T ks)]

/-- ### THE POLARITY CONTROL FOR THE FOLD: a summand that is not even. -/
def fBad : Int → Nat := fun x => if x = 1 then 7 else 0

/-- An even summand, for the positive control. -/
def fGood : Int → Nat := fun x => if x = 1 ∨ x = -1 then 7 else 0

theorem fBad_is_not_even : (fBad (-1) == fBad 1) = false := rfl

theorem fGood_is_even_at_one : fGood (-1) = fGood 1 := rfl

/-- ### WITHOUT EVENNESS THE FOLD FAILS — so the `2` is NOT a free constant; it
    is bought by the evenness and by nothing else. -/
theorem fold_fails_for_fBad :
    (twoEnded fBad [1] == oneSided fBad [1] + oneSided fBad [1]) = false := rfl

/-- With evenness it holds, at the same index list. -/
theorem fold_holds_for_fGood :
    twoEnded fGood [1] = oneSided fGood [1] + oneSided fGood [1] := rfl

/-- ### THE EVENNESS IS LOAD-BEARING, STATED AS AN EXISTENCE CLAIM. -/
theorem fold_needs_evenness :
    ∃ (T : Int → Nat) (S : List Int),
      (twoEnded T S == oneSided T S + oneSided T S) = false :=
  ⟨fBad, [1], fold_fails_for_fBad⟩

end FoldedMirrorShadow
