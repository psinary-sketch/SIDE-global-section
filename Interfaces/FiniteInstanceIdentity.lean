/-
  FILE E of the Mathlib companion (opened at W-CONSTRUCTION-1 act 16):
  THE FINITE-INSTANCE IDENTITY — THE CLOSURE PROTOCOL'S STEP-ONE OBJECT.

  ### THE REGISTER SENTENCE, QUOTED UNCHANGED: "h2 IS THE SINGLE OPEN PREMISE."

  THIS FILE STATES; IT DOES NOT PROVE. This states the identity whose truth at
  complete roster is h2; at finite instance it is checkable; nothing here proves it.

  THE CONSTITUENTS AND THEIR OWNERS (the ledger's addresses, labeled):
  · the ε-regularized archimedean E₁-trace — owner: the ε-lemma's bookkeeping (its
    geometry now DERIVED, act 15: the pair structure whose block inverses are the
    ε-denominators) and files B–C's L²(ℚ_p) for the finite factors;
  · the volume-normalized quotient trace — owner: FILE D (the fixed-orbit count,
    proved longhand act 9, its formalization file D's labeled sorry) with the volume
    normalization forced (act 7, modulo the class-richness lemma at cite);
  · the restricted-tensor assembly — owner: INFRASTRUCTURE (the Hilbert ⊗′; the sharp
    missing lemma stated in GlobalSection.lean);
  · Weil's ledger — the atlas's certified columns at the cell, in the SUPPORT-AND-
    PROGRAM-VOICE convention (`W_∞ = +A`; the prime term enters with a MINUS), which
    is the convention this file's own relation writes.
    ### AMENDED 2026-08-28 (b235) BY AUTHOR RULING. THE ORIGINAL READ:
    ###   "in the CC sign convention (the act-12 dictionary)."
    ### WHY THE ORIGINAL WAS THE DEFECT: this file's relation writes
    ### `wInf - wPrimes`, and under CC's convention that expression is `-A - PR`,
    ### which names NO object the corpus computes. Under the convention now named
    ### it is `A - PR` — the support-and-program layer's own `LEFT` column.
    ### THE ATLAS THAT DECIDED IT: `SIGN_ARRANGEMENT_RECONCILIATION.md` §5, where
    ### EIGHT corpus-voice cells agree and the deciding sentence is the corpus's own
    ### statement of its open premise, at support-voice:
    ###   "h2 — the sign of `W_∞ − W_2`."
    ### CC's `𝒲_∞ = −A` is NOT a dissent but a correctly-translated IMPORT (IMP-2):
    ### CC's eq. (1) puts the zero-sum on the LEFT, so every local term flips sign.

  SORRY COUNT OF THIS FILE: 0 — and, per the 2026-08-19 ruling, EVERY kernel file's.
  The constituents are DATA PARAMETERS (Props over supplied structures), NOT sorried
  declarations; their realizations live in the WORKING LAYER as recorded statements
  (relay/reports/2026-08-19-sorry-ledger-cleared.md) until they can enter proved.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs

namespace FiniteInstanceIdentity

/-- a banked diagonal cell: the window a² > 1. -/
structure DiagonalCell where
  a_sq : ℚ
  one_lt : 1 < a_sq

/-- the ε-regularized archimedean E₁-trace on the constrained class at a cell.
    OWNER: the ε-lemma's bookkeeping (geometry derived, act 15) + files B–C.

    ### `value` IS DEFINED BY AUTHOR RULING, 2026-08-28 (b239). THE RULING, VERBATIM:
    ###   "RULE M-1: C2, per-cell instrument realization standing until M-4 closes;
    ###    Δ₋'s bookkeeping (M-4) named as the definition's open debt in the
    ###    correspondence row."
    ### THE DEFINITION (b237's candidate C2):
    ###   ### **`value := Tr_full + E2 + Δ₋`**
    ### the three archimedean channels of the bench instrument, at a DIAGONAL a² cell:
    ###   `Tr_full` — the prolate mode trace   (`b38_act10.trace_modes`)
    ###   `E2`      — the ε-regularization term (`b38_act10.e2_of_grid`)
    ###   `Δ₋`      — the odd-index `t(n)` series (§17, banked at the `ε′(1⁺)` pin)
    ### This is a DOCUMENTED BINDING, not a Lean definition, and the idiom is chosen
    ### deliberately: ### **the three summands have NO formal definitions in this
    ### repository**, so writing them as terms would mean inventing three realizations
    ### the record does not have. ### THE FIELD STAYS A DATA PARAMETER; WHAT IS FIXED
    ### IS ITS MEANING.
    ### ### THE RIDER, PART OF THE RULING AND NOT A GLOSS ON IT: the realization is
    ### ### **PER-CELL AT BENCH, STANDING UNTIL M-4 CLOSES.** It is not structural.
    ### ### THE OPEN DEBT, NAMED: ### **M-4 — Δ₋'s trace-class bookkeeping.** §17's own
    ### ### grade is "COMPUTED IN STRUCTURE … open only in its trace-class bookkeeping",
    ### ### so ### **`value` IS DEFINED ONLY AS FAR AS THAT BOOKKEEPING IS.** The debt
    ### ### also stands in CORRESPONDENCE.md's grade cell, where the next reader meets it.
    ### THE ORIGINAL DOCSTRING READ, IN FULL:
    ###   "the ε-regularized archimedean E₁-trace on the constrained class at a cell.
    ###    OWNER: the ε-lemma's bookkeeping (geometry derived, act 15) + files B–C."
    ### NOTHING ELSE IN THIS FILE CHANGED: no declaration, no type, no relation, no token
    ### of code. ### A DEFINITION WAS NAMED; NOTHING WAS PROVED AND NOTHING WAS CLOSED. -/
structure ArchimedeanE1Trace (cell : DiagonalCell) where
  value : ℝ

/-- the volume-normalized quotient trace at a cell.
    OWNER: file D (the count) + the forced volume normalization (act 7). -/
structure QuotientTrace (cell : DiagonalCell) where
  value : ℝ

/-- Weil's ledger at the cell: `W_∞` (### SUPPORT-AND-PROGRAM-VOICE convention:
    `wInf = +A`, the archimedean column as the atlas computes it) and the prime sum,
    the atlas's certified columns. The relation below therefore reads `A − PR`.
    ### AMENDED 2026-08-28 (b235). THE ORIGINAL READ:
    ###   "`W_∞` (CC convention, the act-12 dictionary) and the prime sum".
    ### NOTHING ELSE IN THIS FILE CHANGED: no declaration, no type, no relation, no
    ### token of code. ### THE STATEMENT IS UNMOVED; ONLY ITS CONVENTION IS NAMED. -/
structure WeilLedger (cell : DiagonalCell) where
  wInf : ℝ
  wPrimes : ℝ

/-- ### THE FINITE-INSTANCE IDENTITY (STATED, NOT PROVED, NOT CLAIMED):
    the built object's trace equals Weil's ledger on the constrained class at the
    cell. Its truth at complete roster is `h2`; at finite instance it is checkable;
    nothing here proves it. The register moves only via the closure protocol's four
    steps in order — this file is step one's OBJECT (the formal statement), not its
    discharge. -/
def finiteInstanceIdentity {cell : DiagonalCell}
    (T : ArchimedeanE1Trace cell) (Q : QuotientTrace cell)
    (W : WeilLedger cell) : Prop :=
  T.value + Q.value = W.wInf - W.wPrimes

end FiniteInstanceIdentity

#print axioms FiniteInstanceIdentity.finiteInstanceIdentity
