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
    ###   ### **`value := Tr_full + E2 − Δ₋`**
    ### the three archimedean channels of the bench instrument, at a DIAGONAL a² cell:
    ###   `Tr_full` — the prolate mode trace   (`b38_act10.trace_modes`)
    ###   `E2`      — the ε-regularization term (`b38_act10.e2_of_grid`)
    ###   `Δ₋`      — the odd-index `t(n)` series (§17, banked at the `ε′(1⁺)` pin)
    ###
    ### ### AMENDED 2026-08-29 (b244) BY AUTHOR RULING. THE ORIGINAL READ:
    ### ###   "### **`value := Tr_full + E2 + Δ₋`**"
    ### THE RULING, VERBATIM: "RULE Δ₋: D1 — RULE M-1's combination amended to
    ### `T.value := Tr_full + E2 − Δ₋` per §19's own sentence, originals visible, the
    ### M-1 card annotated."
    ### ### THE WARRANT IS §19's OWN ROW FOR THE RAW CHANNEL, QUOTED:
    ### ###   `Tr_∞(ϑ(g)S_Son)` — "AT CONTENT (CC Thm 4.7); **our object's trace = this
    ### ###    − Δ₋(g)**"
    ### ### and act 8's assembly, the only place in the corpus where the combination is
    ### ### written as EXECUTABLE CODE (`b36_act8.py:175`):
    ### ###   `RIGHT = (Tr_full + E2 - Dneg) - Thq`
    ### ### — where the parenthesis is itself the statement of which terms belong to `T`.
    ### ### WHAT DID **NOT** CHANGE, AND IT MATTERS: ### **Δ₋'s DEFINITION AND ITS BINDING
    ### ### ARE UNTOUCHED.** §17's odd-index `t(n)` series, via `b37_act9.eps_masked(rr,
    ### ### odd)`, is what §17/§19 define and is what b240 bound — b241 checked that and
    ### ### recorded it. ### **ONLY THE SIGN IN THE COMBINATION MOVED.**
    ### ### PROVENANCE: A RULING, NOT A DERIVATION. b241 FILED this sign and executed
    ### ### nothing, because an executor does not amend a ruling. The author ruled.
    ###
    ### ### RULE MODES: K1, 2026-08-29 (b244), THE REALIZATION'S CEILING, RULED:
    ### ### **THE DEFINITION STAYS LEMMA F.1's ELEVEN MODES.** ### The per-cell
    ### ### realization reports the ### **SEVEN COMPUTABLE** modes plus ### **A TAIL TERM
    ### ### IN ITS BAR.**
    ### ### WHY, from b242's measurement: `qeps_layer.py:41` certifies eleven terms, but
    ### ### `λ²ₙ` reaches `4.7e−16` at `n = 7`, so ### **float64 CARRIES SEVEN** — and
    ### ### `n_last = 6` at EVERY `NQ` from 500 to 1300, so more quadrature buys no modes.
    ### ### The NQ-spread of the truncated trace jumps ### **61×–249×** exactly when the
    ### ### first sub-floor mode enters the sum. ### **THE CERTIFIED CEILING AND THE
    ### ### ARITHMETIC CEILING ARE NOT THE SAME NUMBER**, and K1 keeps the definition at
    ### ### the former while making the realization honest about the latter.
    ### ### THE TAIL IS **NOT BOUNDED** BY b242 — branch (SLOW), envelope beyond reach,
    ### ### obstruction priced at ~3.45 decimal digits per further mode.
    ### ### `W-ORD-MODE-PRECISION` (K3) is the bounded instrument act that closes it.
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
    OWNER: file D (the count) + the forced volume normalization (act 7).

    ### `value` IS BOUND BY AUTHOR RULING, 2026-08-29 (b244). THE RULING, VERBATIM:
    ###   "RULE Q: O1 — `Q.value := −Θ_q` as documented binding, the five owner texts
    ###    cited, the aggregation still UNSTATED and said so."
    ### THE BINDING:  ### **`value := −Θ_q`**, with `Θ_q` the per-cell quotient sum the
    ### bench instrument returns (`b38_act10.theta_quotient`, on `V_inv`).
    ### ### THE FIVE OWNER TEXTS, CITED AS THE RULING REQUIRES:
    ###   (1) §19's comparison: `W_∞(g) − Σ_p W_p(g) ≟ [Tr_∞(ϑ(g)S_Son) + ∫g ε]
    ###       − Θ_quotient(g)` — Θ_q enters with a MINUS, the prime side's own orientation.
    ###   (2) `b36_act8.py:175`: `RIGHT = (Tr_full + E2 - Dneg) - Thq` — the only place in
    ###       the corpus where the assembly is written as executable code, and `Thq` sits
    ###       OUTSIDE the trace bracket with a MINUS.
    ###   (3) §20(c)'s closed form: `τ_q(p,n,k)·p^{k/2} = (p^n−p^k)/(p^n−1)`, so the
    ###       quotient channel **CONVERGES TO WEIL'S COEFFICIENTS** at the level limit —
    ###       i.e. Θ_q is the model's `Σ_p W_p`, which enters with a minus.
    ###   (4) the recurring pairing `(Θ_q − PR)`, written that way by four independent
    ###       acts: `b36_act8.py`, `b37_act9.py:169-170`, `b38_act10.py:188`, and §20(a)'s
    ###       stated anatomy `D = −resid47 − 2·E2 + Δ₋ + (Θ_q − PR)`.
    ###   (5) this file's own operator below: `T.value + Q.value = W.wInf - W.wPrimes` —
    ###       `Q` enters with a PLUS, so `Q.value = −Θ_q` places Θ_q with the prime side.
    ###
    ### ### AND THE THING THE RULING REQUIRES BE SAID, SAID HERE AND NOT IN A FOOTNOTE:
    ### ### **THE AGGREGATION IS STILL UNSTATED.** ### Indexed at `quotient-trace`, found
    ### ### by b197 and RE-CONFIRMED by b215: ### *"no statement assembles the per-place
    ### ### values into the single real `Q.value` at a cell."*
    ### ### THE FIVE TEXTS ABOVE **ORIENT** `Θ_q` INSIDE THEIR OWN COMPARISONS. ### **NONE
    ### ### OF THEM ASSEMBLES IT INTO `Q.value`, AND THOSE ARE TWO DIFFERENT CLAIMS.**
    ### ### b241 ROUTED THIS QUESTION FOR EXACTLY THAT REASON AND CHOSE NOTHING; the
    ### ### author ruled O1. ### **THE BINDING IS THEREFORE A RULING RESTING ON FIVE
    ### ### ORIENTING TEXTS AND ONE UNCLOSED STEP**, and M-2 (the restricted-product
    ### ### assembly) is where that step lives. ### M-2 IS NOT CLOSED BY THIS BINDING.
    ###
    ### ### DISCLOSED, BECAUSE THE STANDING CLAUSE REQUIRES THE DIRECTION BE NAMED:
    ### ### **O1 SHRINKS THE RESIDUAL** — it is b240's banked variant V2. ### AND IT DOES
    ### ### NOT CLOSE IT: V2 stays **19×–24×** the combined bar and V3 **8.6×–19×**, with
    ### ### the largest term `resid47` untouched by every orientation. ### **A RULING
    ### ### CHOSEN TO MAKE THE COLUMNS MEET WOULD HAVE TO MAKE THEM MEET.**
    ### ### THE FIELD STAYS A DATA PARAMETER; WHAT IS FIXED IS ITS MEANING. -/
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
