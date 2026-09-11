import SmearGeneral

/-!
  # GridTrace -- the model's counting form, related to a grid trace DEFINED HERE.

  THE TWO OBJECTS THIS MODULE RELATES, NAMED IN ITS STATEMENT:
    (1) the model's counting form, `B329.signedTrace p n t` -- b310's signed count,
        multiplied through by `q`, as `FiniteSideSeal` states it; and
    (2) `gridTrace p n t` -- the trace of an operator on functions on the grid
        `Z/p^(2n)` that THIS MODULE DEFINES: `T_t = q A_t - B_t`, where `A_t` has
        kernel `offb s && offb s' && (t s mod N == s')` (the scaling map read
        between off-ball points) and `B_t` has kernel
        `offb s && offb s' && (t s mod N == s' mod q)` (the same map followed by the
        sum over the fibre of reduction modulo `q`). Each trace is the sum of its
        diagonal over the grid; `tr T_t := q tr A_t - tr B_t`, by linearity.

  THE SOURCE'S TRACE IS NOT THIS OBJECT. The source's `Tr(theta(t) Pi)` lives on the
  source's space at the finite place; b310 read it as the signed count, and that
  reading is b310's derivation and is NOT compiled here or anywhere in `Core/`.
  What is compiled is that THIS grid operator's trace equals the model's counting
  form. Where the ferry that ordered this module and the source differ, the source
  governs.

  Lean 4 (v4.29.1, pinned), no Mathlib import; the axiom profile is PRINTED, never
  assumed.
-/

namespace GridTrace
open SmearGeneral

/-- "`x` is off the ball": `q` does not divide `x`. -/
def offb (p n x : Nat) : Bool := !(x % B329.ballQ p n == 0)

/-- The scaling map on the grid: `s -> t s mod N`. -/
def img (p n t s : Nat) : Nat := (t * s) % B329.gridN p n

/-- The kernel of `A_t`. -/
def kerA (p n t s s' : Nat) : Bool := offb p n s && offb p n s' && (img p n t s == s')

/-- The kernel of `B_t`. -/
def kerB (p n t s s' : Nat) : Bool :=
  offb p n s && offb p n s' && (img p n t s % B329.ballQ p n == s' % B329.ballQ p n)

/-- `tr A_t`: the sum of `A_t`'s diagonal over the grid. -/
def trA (p n t : Nat) : Nat := sumf (fun s => ind (kerA p n t s s)) (List.range (B329.gridN p n))

/-- `tr B_t`: the sum of `B_t`'s diagonal over the grid. -/
def trB (p n t : Nat) : Nat := sumf (fun s => ind (kerB p n t s s)) (List.range (B329.gridN p n))

/-- `tr T_t = q tr A_t - tr B_t` -- the grid trace THIS MODULE defines. -/
def gridTrace (p n t : Nat) : Int := (B329.ballQ p n * trA p n t : Int) - (trB p n t : Int)

theorem beq_self' (u : Nat) : (u == u) = true := decide_eq_true rfl

theorem and_false' (x : Bool) : (x && false) = false := by cases x <;> rfl

theorem mul_k_zero {m r k : Nat} (hr : r < m) (h : r = m * k) : k = 0 := by
  cases k with
  | zero => rfl
  | succ k' =>
    have h1 : m ≤ m * (k' + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
      exact Nat.le_add_right m (m * k')
    rw [← h] at h1
    exact absurd (Nat.lt_of_lt_of_le hr h1) (Nat.lt_irrefl r)

theorem mod_self_lt {s m : Nat} (hs : s < m) : s % m = s :=
  mod_unique s m 0 s (Nat.lt_of_le_of_lt (Nat.zero_le s) hs) hs (Nat.zero_add s).symm

/-- With `r, u < m`: `(r + u) mod m` returns `u` exactly when `r = 0`. -/
theorem key (r u m : Nat) (hm : 0 < m) (hr : r < m) (hu : u < m) :
    ((r + u) % m == u) = (r == 0) := by
  cases r with
  | zero =>
    have e : (0 + u) % m = u := mod_unique (0 + u) m 0 u hm hu rfl
    rw [e, beq_self' u]
    rfl
  | succ r' =>
    have hne : ((r' + 1 + u) % m == u) = false := by
      apply ne_beq_false
      intro h
      obtain ⟨k, hk, _⟩ := mod_spec (r' + 1 + u) m hm
      rw [h] at hk
      have h2 : r' + 1 = m * k := B329.add_right_cancel' hk
      have h3 := mul_k_zero hr h2
      rw [h3] at h2
      exact Nat.noConfusion (h2.trans (Nat.mul_zero m))
    rw [hne]
    exact (ne_beq_false (fun h => Nat.noConfusion h)).symm

theorem swap4 (X Y Z W : Nat) : (X + Y) + (Z + W) = (Y + W) + (X + Z) := by
  rw [Nat.add_assoc, Nat.add_comm Y (Z + W), Nat.add_assoc Z W Y, Nat.add_comm W Y,
    ← Nat.add_assoc X Z (Y + W), Nat.add_comm (X + Z) (Y + W)]

/-- `(a + s) mod m` equals `s mod m` exactly when `m` divides `a`. -/
theorem mod_add_iff (a s m : Nat) (hm : 0 < m) : ((a + s) % m == s % m) = (a % m == 0) := by
  obtain ⟨qa, ha, hra⟩ := mod_spec a m hm
  obtain ⟨qs, hs, hrs⟩ := mod_spec s m hm
  have e1 : a + s = (m * qa + a % m) + (m * qs + s % m) := by rw [← ha, ← hs]
  have e : a + s = (a % m + s % m) + m * (qa + qs) := by
    rw [e1, swap4, Nat.mul_add]
  rw [e, add_mul_mod' _ m _ hm]
  exact key (a % m) (s % m) m hm hra hrs

theorem tsub_split (t s : Nat) (ht : 1 ≤ t) : t * s = (t - 1) * s + s := by
  calc t * s = ((t - 1) + 1) * s := by rw [sub_add_cancel' ht]
    _ = (t - 1) * s + s := Nat.succ_mul (t - 1) s

theorem grid_sq (p n : Nat) : B329.gridN p n = B329.ballQ p n * B329.ballQ p n := by
  unfold B329.gridN B329.ballQ
  rw [Nat.two_mul, B329.pow_add']

theorem diagA (p n t s : Nat) (hp : 1 ≤ p) (ht : 1 ≤ t) (hs : s < B329.gridN p n) :
    kerA p n t s s = (!(s % B329.ballQ p n == 0) && !((t * s) % B329.gridN p n % B329.ballQ p n == 0)
      && ((t - 1) * s) % B329.gridN p n == 0) := by
  have hN : 0 < B329.gridN p n := pow_pos' p hp (2 * n)
  have e1 : (img p n t s == s) = (((t - 1) * s) % B329.gridN p n == 0) := by
    unfold img
    rw [tsub_split t s ht]
    have h := mod_add_iff ((t - 1) * s) s (B329.gridN p n) hN
    rw [mod_self_lt hs] at h
    exact h
  unfold kerA
  rw [e1]
  cases hf : (((t - 1) * s) % B329.gridN p n == 0) with
  | false => rw [and_false', and_false']
  | true =>
    have hi : img p n t s = s := beq_true_eq (e1.trans hf)
    unfold img at hi
    unfold offb
    rw [hi]

theorem diagB (p n t s : Nat) (hp : 1 ≤ p) (ht : 1 ≤ t) :
    kerB p n t s s = (!(s % B329.ballQ p n == 0) && !((t * s) % B329.gridN p n % B329.ballQ p n == 0)
      && ((t - 1) * s) % B329.ballQ p n == 0) := by
  have hq : 0 < B329.ballQ p n := pow_pos' p hp n
  have e2 : (img p n t s % B329.ballQ p n == s % B329.ballQ p n) = (((t - 1) * s) % B329.ballQ p n == 0) := by
    unfold img
    rw [grid_sq, mod_mod_of_mul _ _ _ hq hq, tsub_split t s ht]
    exact mod_add_iff ((t - 1) * s) s (B329.ballQ p n) hq
  unfold kerB
  rw [e2]
  cases hf : (((t - 1) * s) % B329.ballQ p n == 0) with
  | false => rw [and_false', and_false']
  | true =>
    have hi : img p n t s % B329.ballQ p n = s % B329.ballQ p n := beq_true_eq (e2.trans hf)
    unfold img at hi
    unfold offb
    rw [hi]

theorem trA_eq (p n t : Nat) (hp : 1 ≤ p) (ht : 1 ≤ t) :
    trA p n t = B329.offBallFixed p n t (B329.gridN p n) := by
  unfold trA B329.offBallFixed
  rw [length_filter_ind]
  apply sumf_congr
  intro s hs
  exact congrArg ind (diagA p n t s hp ht (lt_of_mem_range hs))

theorem trB_eq (p n t : Nat) (hp : 1 ≤ p) (ht : 1 ≤ t) :
    trB p n t = B329.offBallFixed p n t (B329.ballQ p n) := by
  unfold trB B329.offBallFixed
  rw [length_filter_ind]
  apply sumf_congr
  intro s _
  exact congrArg ind (diagB p n t s hp ht)

/-- THE STATEMENT, ITS TWO OBJECTS NAMED: the grid trace this module defines equals the
    model's counting form `B329.signedTrace`, for every `p ≥ 1`, every `n`, every `t ≥ 1`.
    It says nothing about the source's `Tr(theta(t) Pi)`, which is not this object. -/
theorem grid_trace_is_signed_count (p n t : Nat) (hp : 1 ≤ p) (ht : 1 ≤ t) :
    gridTrace p n t = B329.signedTrace p n t := by
  unfold gridTrace B329.signedTrace
  rw [trA_eq p n t hp ht, trB_eq p n t hp ht]

end GridTrace
