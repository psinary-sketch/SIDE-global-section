/-
  THE FINITE-SIDE SEAL · FiniteSideSeal.lean
  ==========================================

  Ferry 2026-09-05 (b329). Vanilla Lean 4 (v4.29.1 pinned), no imports; expected
  profile per terminal: "does not depend on any axioms".

  ### WHAT THIS MODULE CERTIFIES, AND -- FIRST, BECAUSE IT MATTERS MORE --
  ### WHAT IT DOES NOT.

  THE GENERAL AND THE PER-CELL ARE STATED HERE SEPARATELY AND ARE NEVER AVERAGED.
  A reader who takes the whole file for one general theorem, or for one decided
  table, has read it for something it does not say. Each theorem's docstring
  says which it is; the summary is this:

    GENERAL (over every base `p`, level, power and index; by induction, from the
    axiom-free part of the core library and helpers proved here by induction):
      Component 1 -- THE DECOMPOSITION. Every nonzero index modulo a power of
        `p ≥ 2` is uniquely a non-multiple of `p` times a power of `p`, with the
        exponent below the level (`valuation_exists`, `valuation_unique`,
        `exponent_below_level`, `index_decomposes`), and multiplication by the
        index factors through the two parts (`action_factors`). b304 split the
        local multiplicative group into its compact and scaling parts; b309 took
        the scaling part as the powers of the prime.
      Component 2 -- THE SCALING PART'S SILENCE. `p^j - 1` is invertible modulo
        every power of `p`, with the inverse exhibited as a geometric sum
        (`scaling_shift_inverse`, b309: "because `p^j - 1` is invertible"), so
        the fixed-point congruence of `t -> p^j t` forces the index into the
        ball, in either congruence (`scaling_congruence_forces_ball`,
        `scaling_fixed_point_in_ball`, `scaling_fixes_nothing_off_ball`). This
        is the law b309's own module header called uncompiled; b309 decided its
        instances at seven cells.

    PER CELL (decided by finite evaluation over the explicit list `cells`, and
    over no other cell):
      Component 3 -- THE COMPACT PART'S SILENCE. The compressed smear over the
        units vanishes: `q * SUM_u A_N(u) = SUM_u A_q(u)` at each listed cell
        (`compact_smear_vanishes_at_cells`), b304's zero for the constant test
        function on the units in b310's signed-count form; beside it the
        NOT-DEAD witness -- the trace at the identity is `q (p^n - 1)^2`, the
        constrained dimension (`identity_trace_is_the_dimension`, b310's terminal
        restated) -- and b304's own refusal, that the traces at the other units
        are NOT all zero (`traces_not_all_zero_off_identity`).
      The polarity controls for Component 2 are also per cell: a non-identity
        UNIT that fixes an off-ball index exists at the level-two-and-above cells
        (`unit_fixes_offball_at_cells`, `some_unit_fixes_offball_above_level_one`)
        and none exists at the level-one cells
        (`no_unit_fixes_offball_at_level_one`); the ball-forcing is the SCALING
        map's property and not every map's. The general control is the identity
        (`identity_fixes_every_index`).

    WHY COMPONENT 3 IS PER CELL AND NOT GENERAL. b304's derivation of the zero is
    general in `p` and `n`, but it runs through the projection onto the
    unit-invariants of the object's own space -- linear algebra over a cyclotomic
    field -- which vanilla Lean does not decide; and a general proof of the
    integer identity decided here would be new mathematics, which this act is
    forbidden to add. b304 tabulated six cells; the seventh, `(2, 3)`, is
    b309/b310's cell and is decided here by the same arithmetic: a check added,
    not a claim added.

    THE UNAVAILABLE ARM, STATED AND NOT MANUFACTURED. The opposite polarity for
    Component 3 -- a cell at which the constant smear over the units SURVIVES --
    cannot be exhibited, because b304's derivation forbids it at every `p` and
    `n`. NO CONTROL CAN EXIST THERE. This module says so here in words and does
    not pretend a theorem in its place.

    Component 4 -- EXHAUSTIVENESS (`finite_side_silence`): one theorem whose
    hypotheses name exactly which generality applies to which part: for `p ≥ 2`,
    a level `n` and an index `0 < t < p^(2n)`, (a) the decomposition holds,
    GENERAL; (b) the scaling part fixes nothing off the ball, GENERAL; (c) if
    `(p, n)` is in `cells`, the compact part's smear vanishes, PER CELL. Its
    docstring quotes b310's fixed-point sentence from its emitting act.

  THE AXIOM FINDING, AND WHAT IT CHANGED. The core library's lemmas about `∣`,
  `%`, `/` and `Nat.Coprime` -- and even `Nat.mul_assoc` -- carry `propext`
  and `Quot.sound` (measured at this act's probe, relay
  `data/b329_axiom_probe.txt`); `omega`, `simp` and `ac_rfl` carry them too.
  The audit bar is zero axioms. So the general theorems here are stated as
  EQUATIONS WITH THEIR WITNESSES -- "`p` does not divide `u`" is
  `NotDiv p u := ∀ c, u ≠ p * c`; "the congruence `p^j t ≡ t (mod p^m)`" is
  `∃ c, p^j * t = t + p^m * c`; "`t` is in the ball" is `∃ d, t = p^m * d` --
  and proved from the axiom-free part of core plus `mul_assoc'`, `pow_add'`,
  `add_right_cancel'`, `add_left_cancel'`, `multiple_of_add_multiple` and
  `search`, each proved here by induction. THREE REGISTERED BARS ARE NOT MET IN
  THEIR REGISTERED FORM, AND SAID: (T1.4) "`u` coprime to every `p^k`" is not
  compiled -- `Nat.Coprime`'s lemmas carry `propext` -- so primality is used
  nowhere in this file and the general theorems hold for every `p ≥ 2` (a
  residue `p` does not divide is a unit of `Z/p^k` exactly when `p` is prime;
  that identification is the library's and is NOT compiled here); (T1.6)
  `action_factors` is the factorization before reduction modulo `M`; (T2.1) is
  the explicit inverse rather than `Nat.Coprime`. Nothing is sorried and
  nothing is weakened silently.

  WHAT IT DOES NOT CERTIFY. It certifies the arithmetic of the model (the grid
  `Z/p^(2n)`, the ball `p^n Z/p^(2n)`, the object's two conditions read as the
  two congruences) and the COUNTING FORM of the trace. The identification of
  that signed count with the source's `Tr(theta(t) Pi)` is b310's derivation,
  checked at b310 against b304's `trace_scaled` and b309's reduced sum, and IT
  IS NOT COMPILED HERE. The general part's `NotDiv p u` and the decided part's
  `u % p != 0` are the same condition by the library's `Nat.dvd_iff_mod_eq_zero`,
  which carries `propext` and is NOT compiled here either. Nothing here is about
  the archimedean place, where the group is continuous and none of this applies
  (b285). Nothing here decides `M-2`, moves a grade, or says the finite side
  contributes nothing: a distribution is not a trace on a space.

  The definitions `cells`, `gridN`, `ballQ` restate B309's, and `offBallFixed`
  restates B310's, in this namespace (no imports); the restatements were checked
  against the emitting modules' text at the act's extract step.

  Bank: relay `data/b329_the_finite_side_seal.txt`.
  Registration: relay `data/b329_registration_2026-09-05.txt`, sealed before
  any of this existed.
-/

namespace B329

/-- "`p` does not divide `u`", written as an equation's refusal rather than with
    the library's `∣`, whose lemmas carry `propext`. -/
def NotDiv (p u : Nat) : Prop := ∀ c, u ≠ p * c

/-- The banked cells `(p, n)`: b304's six and b309/b310's seventh. B309's list,
    restated. -/
def cells : List (Nat × Nat) := [(2, 1), (2, 2), (3, 1), (3, 2), (5, 1), (7, 1), (2, 3)]

/-- The grid `Z/p^(2n)`. B309's definition, restated. -/
def gridN (p n : Nat) : Nat := p ^ (2 * n)

/-- The ball's modulus `p^n`. B309's definition, restated. -/
def ballQ (p n : Nat) : Nat := p ^ n

/-- The off-ball points that multiplication by `t` fixes modulo `m`, counted.
    B310's definition, restated. -/
def offBallFixed (p n t m : Nat) : Nat :=
  ((List.range (gridN p n)).filter
    (fun s => !(s % ballQ p n == 0)
              && !((t * s) % gridN p n % ballQ p n == 0)
              && ((t - 1) * s) % m == 0)).length

/-- The units of the grid: the residues below `p^(2n)` that `p` does not divide. -/
def units (p n : Nat) : List Nat := (List.range (gridN p n)).filter (fun u => u % p != 0)

/-- `SUM_u A_N(u)` over the units: the grid-congruence counts, summed. -/
def sumAN (p n : Nat) : Nat := (units p n).foldl (fun acc u => acc + offBallFixed p n u (gridN p n)) 0

/-- `SUM_u A_q(u)` over the units: the ball-congruence counts, summed. -/
def sumAQ (p n : Nat) : Nat := (units p n).foldl (fun acc u => acc + offBallFixed p n u (ballQ p n)) 0

/-- b310's signed count at a unit, multiplied through by `q`: `q * A_N(u) - A_q(u)`. -/
def signedTrace (p n u : Nat) : Int :=
  (ballQ p n * offBallFixed p n u (gridN p n) : Int) - (offBallFixed p n u (ballQ p n) : Int)

/-- A non-identity unit `u` fixing an off-ball index `s` in the grid congruence. -/
def unitFixesOffBall (p n u s : Nat) : Bool :=
  (u % p != 0) && (u != 1) && !(s % ballQ p n == 0) && ((u * s) % gridN p n == s)

/-- Whether SOME non-identity unit fixes SOME off-ball index at the cell. -/
def someUnitFixesOffBall (p n : Nat) : Bool :=
  (List.range (gridN p n)).any (fun u =>
    (List.range (gridN p n)).any (fun s => unitFixesOffBall p n u s))

/-- The geometric sum `1 + p^j + p^(2j) + ... + p^((k-1) j)`: the inverse of
    `p^j - 1` modulo `p^(jk)`, up to sign. -/
def geom (p j : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => geom p j k + p ^ (j * k)

/-! ## Helpers, proved by induction because the library's versions carry `propext`. -/

/-- Helper. Associativity of multiplication, by induction. -/
theorem mul_assoc' (a b c : Nat) : a * (b * c) = a * b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ k ih => rw [Nat.mul_succ, Nat.mul_add, ih, Nat.mul_succ]

/-- Helper. `p^(a+b) = p^a * p^b`, by induction. -/
theorem pow_add' (p a b : Nat) : p ^ (a + b) = p ^ a * p ^ b := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ k ih => rw [Nat.add_succ, Nat.pow_succ, ih, Nat.pow_succ, mul_assoc']

/-- Helper. Right cancellation of addition, by induction. -/
theorem add_right_cancel' {a b c : Nat} : a + c = b + c → a = b := by
  induction c with
  | zero => intro h; rw [Nat.add_zero, Nat.add_zero] at h; exact h
  | succ k ih => intro h; rw [Nat.add_succ, Nat.add_succ] at h; exact ih (Nat.succ.inj h)

/-- Helper. Left cancellation of addition. -/
theorem add_left_cancel' {a b c : Nat} (h : a + b = a + c) : b = c := by
  rw [Nat.add_comm a b, Nat.add_comm a c] at h
  exact add_right_cancel' h

/-- Helper. `t + N a = N b` makes `t` a multiple of `N`, by induction on `a`. -/
theorem multiple_of_add_multiple {t N : Nat} : ∀ a b, t + N * a = N * b → ∃ d, t = N * d := by
  intro a
  induction a with
  | zero => intro b h; rw [Nat.mul_zero, Nat.add_zero] at h; exact ⟨b, h⟩
  | succ k ih =>
    intro b h
    cases b with
    | zero =>
      rw [Nat.mul_zero, Nat.mul_succ, ← Nat.add_assoc] at h
      have ht : t + N * k = 0 := Nat.eq_zero_of_add_eq_zero_right h
      exact ⟨0, by rw [Nat.mul_zero]; exact Nat.eq_zero_of_add_eq_zero_right ht⟩
    | succ b' =>
      rw [Nat.mul_succ, Nat.mul_succ, ← Nat.add_assoc] at h
      exact ih b' (add_right_cancel' h)

/-- Helper. A bounded search decides whether `t` is `p` times some `c ≤ b`, by
    induction on the bound, with `Nat.decEq` (axiom-free) at each step. -/
theorem search (t p : Nat) : ∀ b, (∃ c, c ≤ b ∧ t = p * c) ∨ (∀ c, c ≤ b → t ≠ p * c) := by
  intro b
  induction b with
  | zero =>
    cases Nat.decEq t (p * 0) with
    | isTrue h => exact Or.inl ⟨0, Nat.le_refl 0, h⟩
    | isFalse h =>
      apply Or.inr
      intro c hc
      have : c = 0 := Nat.le_antisymm hc (Nat.zero_le c)
      rw [this]
      exact h
  | succ k ih =>
    cases ih with
    | inl h =>
      obtain ⟨c, hc, hct⟩ := h
      exact Or.inl ⟨c, Nat.le_succ_of_le hc, hct⟩
    | inr h =>
      cases Nat.decEq t (p * (k + 1)) with
      | isTrue h2 => exact Or.inl ⟨k + 1, Nat.le_refl _, h2⟩
      | isFalse h2 =>
        apply Or.inr
        intro c hc
        cases Nat.eq_or_lt_of_le hc with
        | inl e => rw [e]; exact h2
        | inr l => exact h c (Nat.le_of_lt_succ l)

/-! ## Component 1 -- THE DECOMPOSITION. GENERAL. (b304's split; b309's `p^j`.) -/

/-- GENERAL. Every positive natural is a non-multiple of `p` times a power of `p`,
    for every `p ≥ 2`. By strong induction: divide out one factor of `p` at a
    time, the bounded `search` deciding whether one is there. b304 split the local
    multiplicative group into compact and scaling parts; this is that split on
    the model's indices. -/
theorem valuation_exists (p : Nat) (hp : 2 ≤ p) :
    ∀ t, 0 < t → ∃ j u, t = u * p ^ j ∧ NotDiv p u := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    cases search t p t with
    | inl h =>
      obtain ⟨k, _, hk⟩ := h
      have hk0 : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0, Nat.mul_zero] at hk
        rw [hk] at ht
        exact Nat.lt_irrefl 0 ht
      have hlt : k < t := by
        have h2 : 2 * k ≤ p * k := Nat.mul_le_mul_right k hp
        have h3 : k < 2 * k := by
          rw [Nat.two_mul]
          exact Nat.lt_add_of_pos_right hk0
        rw [hk]
        exact Nat.lt_of_lt_of_le h3 h2
      obtain ⟨j, u, hju, hu⟩ := ih k hlt hk0
      refine ⟨j + 1, u, ?_, hu⟩
      rw [hk, hju, Nat.pow_succ, Nat.mul_comm p (u * p ^ j), ← mul_assoc']
    | inr h =>
      refine ⟨0, t, ?_, ?_⟩
      · rw [Nat.pow_zero, Nat.mul_one]
      · intro c hc
        cases Nat.lt_or_ge c (t + 1) with
        | inl hlt => exact h c (Nat.le_of_lt_succ hlt) hc
        | inr hge =>
          have h1 : t < c := hge
          have hp1 : 1 ≤ p := Nat.le_trans (by decide) hp
          have h2 : 1 * c ≤ p * c := Nat.mul_le_mul_right c hp1
          rw [Nat.one_mul] at h2
          have h3 : t < p * c := Nat.lt_of_lt_of_le h1 h2
          rw [hc] at h3
          exact Nat.lt_irrefl _ h3

/-- GENERAL. The decomposition is unique: two representations with the same base
    and non-multiple units agree in exponent and unit. By induction on the
    exponent, cancelling one factor of `p` at a time. (b304, b309.) -/
theorem valuation_unique (p u u' : Nat) (hp : 2 ≤ p) (hu : NotDiv p u) (hu' : NotDiv p u') :
    ∀ j j', u * p ^ j = u' * p ^ j' → j = j' ∧ u = u' := by
  intro j
  induction j with
  | zero =>
    intro j' h
    cases j' with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one, Nat.mul_one] at h
      exact ⟨rfl, h⟩
    | succ k =>
      exfalso
      rw [Nat.pow_zero, Nat.mul_one, Nat.pow_succ, mul_assoc', Nat.mul_comm (u' * p ^ k) p] at h
      exact hu (u' * p ^ k) h
  | succ i ih =>
    intro j' h
    cases j' with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.mul_one, Nat.pow_succ, mul_assoc', Nat.mul_comm (u * p ^ i) p] at h
      exact hu' (u * p ^ i) h.symm
    | succ k =>
      rw [Nat.pow_succ, Nat.pow_succ, mul_assoc', mul_assoc'] at h
      have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
      have h2 : u * p ^ i = u' * p ^ k := Nat.eq_of_mul_eq_mul_right hp0 h
      obtain ⟨h3, h4⟩ := ih k h2
      exact ⟨by rw [h3], h4⟩

/-- GENERAL. An index below `p^L` with a positive unit has its exponent below `L`.
    (b309: the exponent ranges below the level.) -/
theorem exponent_below_level {p u j L : Nat} (hp : 2 ≤ p) (hu : 0 < u) (h : u * p ^ j < p ^ L) :
    j < L := by
  apply Nat.lt_of_not_le
  intro hLj
  have h1 : p ^ L ≤ p ^ j := Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) hLj
  have hu1 : 1 ≤ u := hu
  have h2 : 1 * p ^ j ≤ u * p ^ j := Nat.mul_le_mul_right (p ^ j) hu1
  rw [Nat.one_mul] at h2
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.le_trans h1 h2))

/-- GENERAL. THE EXHAUSTIVENESS STATEMENT'S FOUNDATION: for `p ≥ 2`, every index
    `0 < t < p^L` is a non-multiple of `p` times a power of `p` with exponent
    below `L`. (b304's split of the local multiplicative group, on the model.)
    The registered coprimality form of "unit" is NOT compiled -- see the header. -/
theorem index_decomposes {p t L : Nat} (hp : 2 ≤ p) (ht : 0 < t) (hL : t < p ^ L) :
    ∃ j u, j < L ∧ NotDiv p u ∧ t = u * p ^ j := by
  obtain ⟨j, u, hju, hu⟩ := valuation_exists p hp t ht
  have hu0 : 0 < u := by
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hju
    rw [hju] at ht
    exact Nat.lt_irrefl 0 ht
  refine ⟨j, u, ?_, hu, hju⟩
  exact exponent_below_level hp hu0 (by rw [← hju]; exact hL)

/-- GENERAL. Multiplication by `t = u * p^j` is multiplication by the unit after
    multiplication by the power: the action factors through the two parts,
    stated before reduction modulo the grid (the reduction's commuting with
    multiplication is the library's `Nat.mul_mod_mod`, which carries `propext`).
    (b304's split; b309's scaling map.) -/
theorem action_factors {p t u j : Nat} (h : t = u * p ^ j) (s : Nat) :
    t * s = u * (p ^ j * s) := by
  rw [h, mul_assoc']

/-! ## Component 2 -- THE SCALING PART'S SILENCE. GENERAL. (b309's mechanism.) -/

/-- GENERAL. The geometric sum's identity: `p^j * G(k) + 1 = G(k) + p^(jk)`, by
    induction on `k`. This is `(p^j - 1) G(k) = p^(jk) - 1` written without
    subtraction: the inverse b309's mechanism needs, exhibited. (b309.) -/
theorem geom_identity (p j : Nat) : ∀ k, p ^ j * geom p j k + 1 = geom p j k + p ^ (j * k) := by
  intro k
  induction k with
  | zero =>
    show p ^ j * 0 + 1 = 0 + p ^ (j * 0)
    rw [Nat.mul_zero, Nat.mul_zero, Nat.pow_zero]
  | succ k ih =>
    show p ^ j * (geom p j k + p ^ (j * k)) + 1 = (geom p j k + p ^ (j * k)) + p ^ (j * (k + 1))
    rw [Nat.mul_add, Nat.mul_succ, pow_add', Nat.add_right_comm, ih, Nat.mul_comm (p ^ j) (p ^ (j * k))]

/-- GENERAL. `p^j - 1` IS INVERTIBLE MODULO EVERY `p^m`, for `j > 0`, with the
    inverse exhibited: `p^j * S + 1 = S + p^m * c`, i.e. `(p^j - 1) S ≡ -1`.
    b309: *"BECAUSE `p^j - 1` IS INVERTIBLE"*. The registered `Nat.Coprime` form
    is not compiled (its lemmas carry `propext`); this is the same fact with its
    witness. -/
theorem scaling_shift_inverse (p j m : Nat) (hj : 0 < j) :
    ∃ S c, p ^ j * S + 1 = S + p ^ m * c := by
  cases j with
  | zero => exact absurd hj (Nat.lt_irrefl 0)
  | succ j' =>
    refine ⟨geom p (j' + 1) m, p ^ (j' * m), ?_⟩
    rw [geom_identity, Nat.succ_mul, pow_add', Nat.mul_comm (p ^ m)]

/-- GENERAL, IN EITHER CONGRUENCE. If `p^j * t ≡ t (mod p^m)` -- written with its
    witness, `p^j * t = t + p^m * c` -- then `p^m` divides `t`: the fixed-point
    congruence forces the index into the ball. With `m = 2n` this is the grid
    congruence and with `m = n` the ball's -- b309: *"IN EITHER CONGRUENCE"*.
    Over every base, power and modulus. -/
theorem scaling_congruence_forces_ball {p j t m : Nat} (hj : 0 < j)
    (h : ∃ c, p ^ j * t = t + p ^ m * c) : ∃ d, t = p ^ m * d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨S, c', hS⟩ := scaling_shift_inverse p j m hj
  have e1 : t * (p ^ j * S + 1) = t * (S + p ^ m * c') := congrArg (fun x => t * x) hS
  have e2 : S * (p ^ j * t) = S * (t + p ^ m * c) := congrArg (fun x => S * x) hc
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, mul_assoc', Nat.mul_comm t (p ^ j)] at e1
  rw [Nat.mul_comm S (p ^ j * t), Nat.mul_add] at e2
  rw [e2, Nat.mul_comm S t, Nat.add_assoc] at e1
  have e3 := add_left_cancel' e1
  rw [Nat.add_comm, mul_assoc', Nat.mul_comm S (p ^ m), ← mul_assoc',
      mul_assoc' t, Nat.mul_comm t (p ^ m), ← mul_assoc'] at e3
  exact multiple_of_add_multiple (S * c) (t * c') e3

/-- GENERAL. The ball congruence's instance: a fixed point of `t -> p^j t` modulo
    the ball's modulus `p^n` is a multiple of `p^n`. (b309: the second of the two
    congruences.) -/
theorem scaling_fixed_point_in_ball {p n j t : Nat} (hj : 0 < j)
    (h : ∃ c, p ^ j * t = t + ballQ p n * c) : ∃ d, t = ballQ p n * d :=
  scaling_congruence_forces_ball (m := n) hj h

/-- GENERAL, over all bases, levels and powers -- the law B309's header called
    uncompiled, whose instances b309 decided at seven cells: in the model's form,
    an index `t < p^(2n)` fixed by `t -> p^j * t` modulo the grid lies in the
    ball (it is zero). b309: *"THE SCALING MAP HAS NO FIXED POINT OFF THE
    BALL"*. -/
theorem scaling_fixes_nothing_off_ball {p n j t : Nat} (hj : 0 < j) (ht : t < gridN p n)
    (h : ∃ c, p ^ j * t = t + gridN p n * c) : t % ballQ p n = 0 := by
  obtain ⟨d, hd⟩ := scaling_congruence_forces_ball (m := 2 * n) hj h
  cases d with
  | zero =>
    rw [Nat.mul_zero] at hd
    rw [hd]
    exact Nat.zero_mod _
  | succ d' =>
    exfalso
    rw [Nat.mul_succ] at hd
    have hle : gridN p n ≤ t := by
      rw [hd]
      exact Nat.le_add_left _ _
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le ht hle)

/-- GENERAL. The polarity control's general arm: the identity fixes every index,
    in the same congruence form (`1 * t = t + M * 0`). Beside b309's zero, so the
    zero is not a dead operator's. -/
theorem identity_fixes_every_index (t M : Nat) : 1 * t = t + M * 0 := by
  rw [Nat.one_mul, Nat.mul_zero, Nat.add_zero]

/-- PER CELL. The polarity control's decided arm: a NON-IDENTITY UNIT fixing an
    OFF-BALL index exists -- `9` fixes `2` at `(2, 2)`, `28` fixes `3` at `(3, 2)`,
    `17` fixes `4` at `(2, 3)`. So the ball-forcing is the scaling map's property
    and not every map's. (b309's control, decided.) -/
theorem unit_fixes_offball_at_cells :
    unitFixesOffBall 2 2 9 2 = true ∧ unitFixesOffBall 3 2 28 3 = true
      ∧ unitFixesOffBall 2 3 17 4 = true := by
  decide

/-- PER CELL. At each banked cell of level two or above, some non-identity unit
    fixes some off-ball index. (b309's control, decided over the named list.) -/
theorem some_unit_fixes_offball_above_level_one :
    [(2, 2), (3, 2), (2, 3)].all (fun c => someUnitFixesOffBall c.1 c.2) = true := by
  decide

/-- PER CELL, THE OTHER ARM. At each banked level-one cell no non-identity unit
    fixes any off-ball index. Both arms, or the first is a check that cannot fail.
    (b309's control, decided over the named list.) -/
theorem no_unit_fixes_offball_at_level_one :
    [(2, 1), (3, 1), (5, 1), (7, 1)].all (fun c => !(someUnitFixesOffBall c.1 c.2)) = true := by
  decide

/-! ## Component 3 -- THE COMPACT PART'S SILENCE. PER CELL. (b304's zero; b310's form.) -/

set_option maxRecDepth 100000 in
/-- PER CELL, decided over `cells` and no other. The compressed smear over the
    units vanishes: `q * SUM_u A_N(u) = SUM_u A_q(u)` -- b304's zero for the
    constant test function on the units, in b310's signed-count form. b304:
    *"THE SMEARED VALUE EXACTLY 0 AT ALL SIX"*; the seventh cell is b309/b310's,
    decided by the same arithmetic. -/
theorem compact_smear_vanishes_at_cells :
    cells.all (fun c => ballQ c.1 c.2 * sumAN c.1 c.2 == sumAQ c.1 c.2) = true := by
  decide

/-- PER CELL. THE NOT-DEAD WITNESS: the signed count at the identity is
    `q * (p^n - 1)^2`, the constrained dimension -- b310's terminal
    `signed_count_at_the_identity_is_the_dimension`, restated in this namespace.
    b310: *"at `t = 1` every off-ball point is fixed and the count is
    `(p^n - 1)^2`"*. -/
theorem identity_trace_is_the_dimension :
    cells.all (fun c =>
      ballQ c.1 c.2 * offBallFixed c.1 c.2 1 (gridN c.1 c.2)
        == ballQ c.1 c.2 * (ballQ c.1 c.2 - 1) * (ballQ c.1 c.2 - 1)
            + offBallFixed c.1 c.2 1 (ballQ c.1 c.2)) = true := by
  decide

/-- PER CELL. b304's own refusal, decided: at each listed cell some NON-IDENTITY
    unit has a NONZERO signed trace, so the object is not identically dead and
    the zero above is the constant function's alone. b304: *"AND THOSE TRACES
    ARE NOT ALL ZERO"*. -/
theorem traces_not_all_zero_off_identity :
    cells.all (fun c =>
      ((units c.1 c.2).filter (fun u => u != 1)).any (fun u => signedTrace c.1 c.2 u != 0)) = true := by
  decide

/-! ## Component 4 -- EXHAUSTIVENESS. Hypotheses name the generality. -/

set_option maxRecDepth 100000 in
/-- EXHAUSTIVENESS, with its generality in its hypotheses. For `p ≥ 2`, a level
    `n` and an index `0 < t < p^(2n)`:
    (a) GENERAL -- `t = u * p^j` with `j < 2n` and `p` not dividing `u`
        (Component 1);
    (b) GENERAL -- for every `j > 0`, if `p^j * t ≡ t` modulo the grid, with its
        witness, then `t` is in the ball (Component 2);
    (c) PER CELL -- if `(p, n)` is in `cells`, `q * SUM_u A_N(u) = SUM_u A_q(u)`
        (Component 3), with the cell list as the hypothesis, each cell decided.

    b310, from its emitting act: *"`Tr(theta(t) Pi)` IS A SIGNED COUNT OF THE
    OFF-BALL POINTS `t` FIXES, IN THE TWO CONGRUENCES THE OBJECT'S TWO
    CONDITIONS IMPOSE, WEIGHTED BY THE EMBEDDING'S HAAR FACTOR."* The counting
    form is what is compiled; the identification with the source's trace is
    b310's derivation and is not. -/
theorem finite_side_silence {p n t : Nat} (hp : 2 ≤ p) (ht : 0 < t) (htN : t < gridN p n) :
    (∃ j u, j < 2 * n ∧ NotDiv p u ∧ t = u * p ^ j)
    ∧ (∀ j, 0 < j → (∃ c, p ^ j * t = t + gridN p n * c) → t % ballQ p n = 0)
    ∧ ((p, n) ∈ cells → ballQ p n * sumAN p n = sumAQ p n) := by
  refine ⟨index_decomposes hp ht htN,
          fun j hj h => scaling_fixes_nothing_off_ball hj htN h,
          fun hc => ?_⟩
  rcases hc with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hc⟩⟩⟩⟩⟩⟩⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · cases hc

end B329

-- The terminals, printed in the order the file states them.
#print axioms B329.mul_assoc'
#print axioms B329.pow_add'
#print axioms B329.add_right_cancel'
#print axioms B329.add_left_cancel'
#print axioms B329.multiple_of_add_multiple
#print axioms B329.search
#print axioms B329.valuation_exists
#print axioms B329.valuation_unique
#print axioms B329.exponent_below_level
#print axioms B329.index_decomposes
#print axioms B329.action_factors
#print axioms B329.geom_identity
#print axioms B329.scaling_shift_inverse
#print axioms B329.scaling_congruence_forces_ball
#print axioms B329.scaling_fixed_point_in_ball
#print axioms B329.scaling_fixes_nothing_off_ball
#print axioms B329.identity_fixes_every_index
#print axioms B329.unit_fixes_offball_at_cells
#print axioms B329.some_unit_fixes_offball_above_level_one
#print axioms B329.no_unit_fixes_offball_at_level_one
#print axioms B329.compact_smear_vanishes_at_cells
#print axioms B329.identity_trace_is_the_dimension
#print axioms B329.traces_not_all_zero_off_identity
#print axioms B329.finite_side_silence
