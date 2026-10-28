/-!
# Every Remainder Everywhere

For every `N ≥ 1`, every `w` with `3 ∤ w`, every `r` and every `B`, there is `n > B` with
`n ≡ r (mod N)` whose Collatz orbit reaches `w`. Theorem: `every_remainder_everywhere`.
No imports; Lean core only.
-/

namespace ERE

/-- The Collatz map. -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `iter f k n` is the `k`-th iterate of `f` at `n`. -/
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

theorem iter_add (f : Nat → Nat) (m n : Nat) : ∀ x, iter f (m + n) x = iter f m (iter f n x) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih (f x)

/-- `Reaches v n` -/
def Reaches (v n : Nat) : Prop := ∃ k, iter collatz k n = v

theorem collatz_double (a : Nat) : collatz (2 * a) = a := by
  unfold collatz; split <;> omega

theorem reaches_trans {a b c : Nat} (h1 : Reaches b a) (h2 : Reaches c b) : Reaches c a := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [iter_add, hk1, hk2]⟩

/-- The backward tree of `v` -/
inductive Tree (v : Nat) : Nat → Prop
  | seed : Tree v v
  | D {n : Nat} : Tree v n → Tree v (2 * n)
  | U {n : Nat} : Tree v n → n % 6 = 4 → ((n - 1) / 3) % 3 ≠ 0 → Tree v ((n - 1) / 3)

theorem tree_reaches {v n : Nat} (h : Tree v n) : Reaches v n := by
  induction h with
  | seed => exact ⟨0, rfl⟩
  | @D n _ ih =>
    exact reaches_trans (⟨1, by simp [iter, collatz_double]⟩ : Reaches n (2 * n)) ih
  | @U n _ h6 _ ih =>
    have h1 : collatz ((n - 1) / 3) = n := by
      unfold collatz; split <;> omega
    exact reaches_trans (⟨1, by simpa [iter] using h1⟩ : Reaches n ((n - 1) / 3)) ih

theorem tree_odd_inv {v n : Nat} (hv : v % 2 = 0) (h : Tree v n) (hodd : n % 2 = 1) :
    ∃ m, Tree v m ∧ m % 6 = 4 ∧ ((m - 1) / 3) % 3 ≠ 0 ∧ n = (m - 1) / 3 := by
  cases h with
  | seed => omega
  | D _ => omega
  | U hm h6 h3 => exact ⟨_, hm, h6, h3, rfl⟩

theorem three_dvd_pow (K : Nat) : 3 ∣ 3 ^ (K + 1) := ⟨3 ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩

theorem one_lt_pow3 (K : Nat) : 1 < 3 ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by decide)

theorem live_mod {m c : Nat} (h3 : 3 ∣ m) (hc : c % 3 ≠ 0) : c % m % 3 ≠ 0 := by
  rw [Nat.mod_mod_of_dvd c h3]; exact hc

theorem four_pow_mod_three (j : Nat) : 4 ^ j % 3 = 1 := by
  induction j with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem two_pow_mod_three_ne (E : Nat) : 2 ^ E % 3 ≠ 0 := by
  induction E with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem pow3_form {j u : Nat} (hj : 1 ≤ j) (hu : u % 3 ≠ 0) :
    ∀ n : Nat, ∃ w : Nat, w % 3 ≠ 0 ∧ (1 + 3 ^ j * u) ^ (3 ^ n) = 1 + 3 ^ (j + n) * w := by
  intro n
  induction n with
  | zero => exact ⟨u, hu, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hx⟩ := ih
    obtain ⟨k', hk'⟩ : ∃ k', j + n = k' + 1 := ⟨j + n - 1, by omega⟩
    refine ⟨w + 3 * (3 ^ k' * w ^ 2 + (3 ^ k') ^ 2 * w ^ 3), ?_, ?_⟩
    · generalize (3 ^ k' * w ^ 2 + (3 ^ k') ^ 2 * w ^ 3) = B
      omega
    · rw [Nat.pow_succ, Nat.pow_mul, hx, hk']
      have e2 : j + (n + 1) = k' + 2 := by omega
      have e3 : 3 ^ (k' + 1) = 3 * 3 ^ k' := by rw [Nat.pow_succ]; grind
      have e4 : 3 ^ (k' + 2) = 9 * 3 ^ k' := by rw [Nat.pow_succ, e3]; grind
      rw [e2, e3, e4]
      generalize 3 ^ k' = a
      grind

theorem pow_one_add (s w : Nat) :
    ∀ n : Nat, ∃ z : Nat, (1 + 3 ^ s * w) ^ n = 1 + n * (3 ^ s * w) + 3 ^ (2 * s) * z := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨n * w ^ 2 + z + z * (3 ^ s * w), ?_⟩
    rw [Nat.pow_succ, hz, Nat.two_mul, Nat.pow_add]
    generalize 3 ^ s = a
    grind

/-- `4^m ≡ 1 (mod 3^(K+1))` exactly when `3^K ∣ m`. -/
theorem four_pow_mod_eq_one_iff {K m : Nat} : 4 ^ m % 3 ^ (K + 1) = 1 ↔ 3 ^ K ∣ m := by
  induction K generalizing m with
  | zero => simp [four_pow_mod_three]
  | succ K ih =>
    have hK3 : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by grind
    have hpos : 0 < 3 ^ K := Nat.pow_pos (by decide)
    constructor
    · intro h
      have h1 : 4 ^ m % 3 ^ (K + 1) = 1 := by
        rw [← Nat.mod_mod_of_dvd (4 ^ m) (Nat.pow_dvd_pow 3 (by omega : K + 1 ≤ K + 1 + 1)), h]
        exact Nat.mod_eq_of_lt (one_lt_pow3 _)
      obtain ⟨k, hk⟩ := ih.1 h1
      subst hk
      by_cases h3k : k % 3 = 0
      · obtain ⟨k', rfl⟩ : 3 ∣ k := Nat.dvd_of_mod_eq_zero h3k
        exact ⟨k', by grind⟩
      · exfalso
        obtain ⟨w, hw, hx⟩ := pow3_form (j := 1) (u := 1) (by omega) (by omega) K
        obtain ⟨z, hz⟩ := pow_one_add (K + 1) w k
        have e4 : 4 ^ (3 ^ K * k) = (4 ^ 3 ^ K) ^ k := by rw [Nat.pow_mul]
        have e5 : (4 : Nat) = 1 + 3 ^ 1 * 1 := by decide
        rw [e4, e5, hx, show 1 + K = K + 1 by omega, hz] at h
        have hb : 1 + k * (3 ^ (K + 1) * w) + 3 ^ (2 * (K + 1)) * z
            = 1 + 3 ^ (K + 1) * (k * w + 3 ^ (K + 1) * z) := by
          have e : (3:Nat) ^ (2 * (K + 1)) = (3 ^ (K + 1)) ^ 2 := by rw [Nat.mul_comm, Nat.pow_mul]
          rw [e]; generalize 3 ^ (K + 1) = a; grind
        rw [hb, hK3] at h
        have hlt : 1 < 3 * 3 ^ (K + 1) := by have := one_lt_pow3 K; omega
        have hdiv : (3 * 3 ^ (K + 1)) ∣ 3 ^ (K + 1) * (k * w + 3 ^ (K + 1) * z) := by
          have := Nat.mod_eq_of_lt hlt
          have h2 : (1 + 3 ^ (K + 1) * (k * w + 3 ^ (K + 1) * z)) % (3 * 3 ^ (K + 1)) = 1 := h
          have := Nat.sub_mod_eq_zero_of_mod_eq (h2.trans (Nat.mod_eq_of_lt hlt).symm)
          simpa using Nat.dvd_of_mod_eq_zero this
        have hdiv2 : 3 ∣ k * w + 3 ^ (K + 1) * z := by
          rw [Nat.mul_comm 3 (3 ^ (K + 1))] at hdiv
          exact Nat.dvd_of_mul_dvd_mul_left (by have := one_lt_pow3 K; omega) hdiv
        have h31 : 3 ∣ 3 ^ (K + 1) * z := Nat.dvd_trans (three_dvd_pow K) (Nat.dvd_mul_right _ _)
        have h32 : 3 ∣ k * w := (Nat.dvd_add_right h31).1 (by rwa [Nat.add_comm] at hdiv2)
        have := Nat.mod_eq_zero_of_dvd h32
        rw [Nat.mul_mod] at this
        have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
        have hw3 : w % 3 = 1 ∨ w % 3 = 2 := by omega
        rcases hk3 with h' | h' <;> rcases hw3 with h'' | h'' <;> simp [h', h''] at this
    · rintro ⟨k, hk⟩
      have hK3' : 3 ^ (K + 1 + 1) = 9 * 3 ^ K := by
        rw [Nat.pow_succ, Nat.pow_succ]; grind
      have hK2 : 3 ^ (K + 1) = 3 * 3 ^ K := by rw [Nat.pow_succ]; grind
      have hm' : 3 ^ K ∣ 3 ^ K * k := ⟨k, rfl⟩
      have h1 : 4 ^ (3 ^ K * k) % 3 ^ (K + 1) = 1 := ih.2 hm'
      have hdm := Nat.div_add_mod (4 ^ (3 ^ K * k)) (3 ^ (K + 1))
      rw [h1] at hdm
      obtain ⟨t, ht⟩ : ∃ t, 4 ^ (3 ^ K * k) = 3 ^ (K + 1) * t + 1 := ⟨_, hdm.symm⟩
      rw [hK2] at ht
      have hm : m = 3 * (3 ^ K * k) := by rw [hk, hK2]; grind
      have e : 4 ^ m = (4 ^ (3 ^ K * k)) ^ 3 := by rw [hm, Nat.mul_comm 3, Nat.pow_mul]
      have hgt : 1 < 3 ^ (K + 1 + 1) := one_lt_pow3 _
      rw [e, ht, hK3']
      have : (3 * 3 ^ K * t + 1) ^ 3 = 1 + 9 * 3 ^ K * (t + 3 * 3 ^ K * t ^ 2 + 3 * (3 ^ K) ^ 2 * t ^ 3) := by
        generalize 3 ^ K = a; grind
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      rw [← hK3']; exact hgt

/-- `2^m ≡ 1 (mod 3^(K+1))` exactly when `2·3^K ∣ m`. -/
theorem two_pow_mod_eq_one_iff {K m : Nat} : 2 ^ m % 3 ^ (K + 1) = 1 ↔ 2 * 3 ^ K ∣ m := by
  constructor
  · intro h
    have h3 : 2 ^ m % 3 = 1 := by
      rw [← Nat.mod_mod_of_dvd (2 ^ m) (three_dvd_pow K), h]
    have hev : m % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h0 | hodd
      · exact h0
      exfalso
      obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
      have e : 2 ^ (2 * n + 1) = 2 * 4 ^ n := by
        rw [Nat.pow_succ, Nat.pow_mul]; grind
      have h4 := four_pow_mod_three n
      rw [e] at h3
      omega
    obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    have e : 2 ^ (2 * n) = 4 ^ n := by rw [Nat.pow_mul]
    rw [e] at h
    exact Nat.mul_dvd_mul_left 2 (four_pow_mod_eq_one_iff.1 h)
  · rintro ⟨q, rfl⟩
    have h : 4 ^ (3 ^ K) % 3 ^ (K + 1) = 1 := four_pow_mod_eq_one_iff.2 (Nat.dvd_refl _)
    have e : 2 ^ (2 * 3 ^ K * q) = (4 ^ (3 ^ K)) ^ q := by
      rw [Nat.mul_assoc, Nat.pow_mul 2 2 (3 ^ K * q), ← Nat.pow_mul 4 (3 ^ K) q]
      try rfl
    rw [e, Nat.pow_mod, h, Nat.one_pow]
    exact Nat.mod_eq_of_lt (one_lt_pow3 K)

theorem mod_cancel_mul_left {m a x y : Nat} (hcop : Nat.Coprime m a) (hxy : y ≤ x)
    (h : (a * x) % m = (a * y) % m) : x % m = y % m := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h2 : a * x - a * y = a * (x - y) := (Nat.mul_sub a x y).symm
  rw [h2] at h1
  have h3 : m ∣ a * (x - y) := Nat.dvd_of_mod_eq_zero h1
  have h4 : m ∣ x - y := Nat.Coprime.dvd_of_dvd_mul_left hcop h3
  have h5 := Nat.mod_eq_zero_of_dvd h4
  have h6 : x = y + (x - y) := by omega
  rw [h6, Nat.add_mod, h5]; simp

theorem two_pow_inj {K E1 E2 : Nat} (h1 : E1 < 2 * 3 ^ K) (h2 : E2 < 2 * 3 ^ K)
    (h : 2 ^ E1 % 3 ^ (K + 1) = 2 ^ E2 % 3 ^ (K + 1)) : E1 = E2 := by
  have key : ∀ a b : Nat, a ≤ b → b < 2 * 3 ^ K →
      2 ^ a % 3 ^ (K + 1) = 2 ^ b % 3 ^ (K + 1) → a = b := by
    intro a b hab hb h
    have hcop : Nat.Coprime (3 ^ (K + 1)) (2 ^ a) := Nat.Coprime.pow (K + 1) a (by decide)
    have hb' : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← Nat.pow_add]; congr 1; omega
    have h' : (2 ^ a * 2 ^ (b - a)) % 3 ^ (K + 1) = (2 ^ a * 1) % 3 ^ (K + 1) := by
      rw [← hb', Nat.mul_one]; exact h.symm
    have hpos : 1 ≤ 2 ^ (b - a) := Nat.pow_pos (by decide)
    have h'' := mod_cancel_mul_left hcop hpos h'
    have hd := two_pow_mod_eq_one_iff.1 (by rw [h'']; exact Nat.mod_eq_of_lt (one_lt_pow3 K))
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  rcases Nat.le_total E1 E2 with hle | hle
  · exact key _ _ hle h2 h
  · exact (key _ _ hle h1 h.symm).symm

theorem four_pow_form (n : Nat) : ∃ q : Nat, 4 ^ (3 ^ n) = 1 + 3 ^ (n + 1) + 3 ^ (n + 2) * q := by
  induction n with
  | zero => exact ⟨0, by decide⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q + 3 ^ n * (1 + 3 * q) ^ 2 + (3 ^ n) ^ 2 * (1 + 3 * q) ^ 3, ?_⟩
    rw [Nat.pow_succ 3 n, Nat.pow_mul, hq]
    grind

/-- `4^(3^(K-1)) ≡ 1 + 3^K (mod 3^(K+1))`. -/
theorem four_pow_cong {K : Nat} (hK : 1 ≤ K) :
    4 ^ (3 ^ (K - 1)) % 3 ^ (K + 1) = (1 + 3 ^ K) % 3 ^ (K + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨q, hq⟩ := four_pow_form n
  rw [hq]
  show (1 + 3 ^ (n + 1) + 3 ^ (n + 2) * q) % 3 ^ (n + 2) = (1 + 3 ^ (n + 1)) % 3 ^ (n + 2)
  exact Nat.add_mul_mod_self_left _ _ _

theorem coprime3 {c : Nat} (hc : c % 3 ≠ 0) : Nat.Coprime 3 c := by
  unfold Nat.Coprime
  rw [Nat.gcd_rec]
  have : c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases this with h | h <;> rw [h] <;> decide

theorem unit_mul {x y : Nat} (hx : x % 3 ≠ 0) (hy : y % 3 ≠ 0) : (x * y) % 3 ≠ 0 := by
  rw [Nat.mul_mod]
  have hx' : x % 3 = 1 ∨ x % 3 = 2 := by omega
  have hy' : y % 3 = 1 ∨ y % 3 = 2 := by omega
  rcases hx' with h | h <;> rcases hy' with h' | h' <;> simp [h, h']

theorem mod_cancel_mul_right {m c x y : Nat} (hcop : Nat.Coprime m c)
    (h : (x * c) % m = (y * c) % m) : x % m = y % m := by
  rcases Nat.le_total y x with hle | hle
  · exact mod_cancel_mul_left hcop hle (by rwa [Nat.mul_comm c x, Nat.mul_comm c y])
  · exact (mod_cancel_mul_left hcop hle (by rw [Nat.mul_comm c x, Nat.mul_comm c y]; exact h.symm)).symm

/-- For live `c, d`, some `2^j c` is congruent to `d` modulo `3^(K+1)`. -/
theorem two_transitive {K c d : Nat} (hc : c % 3 ≠ 0) (hd : d % 3 ≠ 0)
    (hdl : d < 3 ^ (K + 1)) : ∃ j, (2 ^ j * c) % 3 ^ (K + 1) = d := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, (2 ^ j * c) % 3 ^ (K + 1) ≠ d := fun j hj => hno ⟨j, hj⟩
  have hcop : Nat.Coprime (3 ^ (K + 1)) c := Nat.Coprime.pow_left (K + 1) (coprime3 hc)
  let U : List Nat := (List.range (3 ^ (K + 1))).filter (fun w => decide (w % 3 ≠ 0))
  let L1 : List Nat := (List.range (2 * 3 ^ K)).map (fun E => (2 ^ E * c) % 3 ^ (K + 1))
  have hUnodup : U.Nodup := List.Pairwise.filter _ List.nodup_range
  have hL1nodup : L1.Nodup := by
    unfold L1
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ (List.nodup_range)
    intro a b ha hb hab heq
    rw [List.mem_range] at ha hb
    have h1 := mod_cancel_mul_right hcop heq
    exact hab (two_pow_inj ha hb h1)
  have hL1U : L1 ⊆ U := by
    intro w hw
    unfold L1 at hw
    rw [List.mem_map] at hw
    obtain ⟨E, _, rfl⟩ := hw
    unfold U
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have := live_mod (three_dvd_pow K) (unit_mul (two_pow_mod_three_ne E) hc)
    simpa using this
  have hdU : d ∈ U := by
    unfold U; rw [List.mem_filter, List.mem_range]; exact ⟨hdl, by simpa using hd⟩
  have hdL1 : d ∉ L1 := by
    unfold L1
    intro h
    rw [List.mem_map] at h
    obtain ⟨E, _, hE⟩ := h
    exact hno' E hE
  have hcons : (d :: L1).Nodup := List.nodup_cons.2 ⟨hdL1, hL1nodup⟩
  have hcsub : (d :: L1) ⊆ U := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hdU
    · exact hL1U hw
  have hlen1 : (d :: L1).length ≤ U.length := hcons.length_le_of_subset hcsub
  have hUsub : U ⊆ (List.range (2 * 3 ^ K)).map (fun j => 3 * (j / 2) + 1 + j % 2) := by
    intro w hw
    unfold U at hw
    rw [List.mem_filter, List.mem_range] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw2' : w % 3 ≠ 0 := by simpa using hw2
    rw [List.mem_map]
    refine ⟨2 * (w / 3) + (w % 3 - 1), ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega
  have hlen2 : U.length ≤ 2 * 3 ^ K := by
    have := hUnodup.length_le_of_subset hUsub
    simpa using this
  have hL1len : L1.length = 2 * 3 ^ K := by simp [L1]
  simp only [List.length_cons] at hlen1
  omega

section Residues
variable (M : Nat) [NeZero M]

/-- The class of `n` in `ℤ/M`. -/
def res (n : Nat) : Fin M := Fin.ofNat M n

theorem res_val (n : Nat) : (res M n).val = n % M := Fin.val_ofNat M n

theorem res_eq_iff (a b : Nat) : res M a = res M b ↔ a % M = b % M := by
  constructor
  · intro h; have := congrArg Fin.val h; rwa [res_val, res_val] at this
  · intro h; apply Fin.ext; rw [res_val, res_val]; exact h

theorem res_add (a b : Nat) : res M (a + b) = res M a + res M b := by
  apply Fin.ext; rw [Fin.val_add, res_val, res_val, res_val, Nat.add_mod]

theorem res_mul (a b : Nat) : res M (a * b) = res M a * res M b := by
  apply Fin.ext; rw [Fin.val_mul, res_val, res_val, res_val, Nat.mul_mod]

theorem res_zero : res M 0 = (0 : Fin M) := rfl
theorem res_one : res M 1 = (1 : Fin M) := rfl
theorem res_two : res M 2 = (2 : Fin M) := rfl
theorem res_three : res M 3 = (3 : Fin M) := rfl
theorem res_four : res M 4 = (4 : Fin M) := rfl

/-- `2` and `3` are units of `ℤ/M`. -/
class Inv23 (M : Nat) [NeZero M] : Prop where
  two : ∃ b : Fin M, (2 : Fin M) * b = 1
  three : ∃ b : Fin M, (3 : Fin M) * b = 1

open Classical in
/-- The inverse of a unit (and `0` for a non-unit). -/
noncomputable def finv (a : Fin M) : Fin M := if h : ∃ b : Fin M, a * b = 1 then h.choose else 0

theorem mul_finv {a : Fin M} (h : ∃ b : Fin M, a * b = 1) : a * finv M a = 1 := by
  unfold finv
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd h h'

theorem two_mul_finv [Inv23 M] : (2 : Fin M) * finv M 2 = 1 := mul_finv M Inv23.two
theorem three_mul_finv [Inv23 M] : (3 : Fin M) * finv M 3 = 1 := mul_finv M Inv23.three

theorem cancel_unit {u v a b : Fin M} (hu : u * v = 1) (h : u * a = u * b) : a = b := by
  calc a = (u * v) * a := by rw [hu]; grind
    _ = v * (u * a) := by grind
    _ = v * (u * b) := by rw [h]
    _ = (u * v) * b := by grind
    _ = b := by rw [hu]; grind

/-- `a` is a unit of `ℤ/M`. -/
def IsU (a : Fin M) : Prop := ∃ b : Fin M, a * b = 1

theorem isU_mul {a b : Fin M} (ha : IsU M a) (hb : IsU M b) : IsU M (a * b) := by
  obtain ⟨ia, hia⟩ := ha
  obtain ⟨ib, hib⟩ := hb
  exact ⟨ib * ia, by
    calc a * b * (ib * ia) = (a * ia) * (b * ib) := by grind
      _ = 1 := by rw [hia, hib]; grind⟩

theorem finv_eq_of_mul {a b : Fin M} (h : a * b = 1) : finv M a = b :=
  cancel_unit M h ((mul_finv M ⟨b, h⟩).trans h.symm)

theorem isU_finv {a : Fin M} (h : IsU M a) : IsU M (finv M a) :=
  ⟨a, by have := mul_finv M h; grind⟩

theorem one_ne_zero_of_one_lt (hM : 1 < M) : (1 : Fin M) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [← res_one M, ← res_zero M, res_val, res_val, Nat.mod_eq_of_lt hM, Nat.zero_mod] at this
  omega

theorem three_ne_zero [Inv23 M] (hM : 1 < M) : (3 : Fin M) ≠ 0 := by
  intro h
  have h3 := three_mul_finv M
  rw [h] at h3
  exact one_ne_zero_of_one_lt M hM (by rw [← h3]; grind)

end Residues

section Counting
variable {M : Nat}

open Classical in
/-- The number of elements of a subset of `ℤ/M`. -/
noncomputable def card (S : Fin M → Prop) : Nat :=
  ((List.finRange M).filter (fun t => decide (S t))).length

open Classical in
theorem mem_cardlist {S : Fin M → Prop} {t : Fin M} :
    t ∈ (List.finRange M).filter (fun t => decide (S t)) ↔ S t := by
  rw [List.mem_filter]; simp [List.mem_finRange]

open Classical in
theorem card_le_of_inj {S T : Fin M → Prop} (g : Fin M → Fin M)
    (hinj : ∀ a b, g a = g b → a = b) (hmap : ∀ t, S t → T (g t)) : card S ≤ card T := by
  unfold card
  have hnd : ((List.finRange M).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange M)
  have hnd2 : (((List.finRange M).filter (fun t => decide (S t))).map g).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ hnd
    intro a b _ _ hab hg
    exact hab (hinj a b hg)
  have hsub : ((List.finRange M).filter (fun t => decide (S t))).map g
      ⊆ (List.finRange M).filter (fun t => decide (T t)) := by
    intro u hu
    rw [List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [mem_cardlist] at ht ⊢
    exact hmap t ht
  have := hnd2.length_le_of_subset hsub
  simpa using this

open Classical in
theorem card_eq_of_sub {S T : Fin M → Prop} (hsub : ∀ t, S t → T t) (hc : card T ≤ card S) :
    ∀ t, T t → S t := by
  intro t0 ht0
  apply Classical.byContradiction
  intro hn
  unfold card at hc
  have hnd : ((List.finRange M).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange M)
  have hnd2 : (t0 :: (List.finRange M).filter (fun t => decide (S t))).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun h => hn ((mem_cardlist).1 h), hnd⟩
  have hsub2 : (t0 :: (List.finRange M).filter (fun t => decide (S t)))
      ⊆ (List.finRange M).filter (fun t => decide (T t)) := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (mem_cardlist).2 ht0
    · exact (mem_cardlist).2 (hsub u ((mem_cardlist).1 hu))
  have := hnd2.length_le_of_subset hsub2
  simp only [List.length_cons] at this
  omega

open Classical in
theorem card_pos {S : Fin M → Prop} {t0 : Fin M} (h : S t0) : 1 ≤ card S := by
  unfold card
  exact List.length_pos_of_mem ((mem_cardlist).2 h)

theorem card_congr {S T : Fin M → Prop} (h : ∀ t, S t ↔ T t) : card S = card T := by
  have : S = T := funext (fun t => propext (h t))
  rw [this]

end Counting

theorem exists_inv_of_coprime {M : Nat} [NeZero M] (a : Fin M) (hcop : Nat.Coprime M a.val) :
    ∃ b : Fin M, a * b = 1 := by
  have hinj : ∀ s t : Fin M, a * s = a * t → s = t := by
    intro s t h
    have h1 := congrArg Fin.val h
    rw [Fin.val_mul, Fin.val_mul] at h1
    have h2 : (s.val * a.val) % M = (t.val * a.val) % M := by
      rw [Nat.mul_comm s.val, Nat.mul_comm t.val]; exact h1
    have h3 := mod_cancel_mul_right hcop h2
    rw [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] at h3
    exact Fin.ext h3
  have hc : card (fun _ : Fin M => True) ≤ card (fun t : Fin M => ∃ s, a * s = t) :=
    card_le_of_inj (fun t => a * t) hinj (fun t _ => ⟨t, rfl⟩)
  exact card_eq_of_sub (S := fun t : Fin M => ∃ s, a * s = t) (T := fun _ : Fin M => True)
    (fun _ _ => trivial) hc 1 trivial

theorem exists_inv_res {M : Nat} [NeZero M] (n : Nat) (hcop : Nat.Coprime M n) :
    ∃ b : Fin M, res M n * b = 1 := by
  apply exists_inv_of_coprime
  rw [res_val]
  unfold Nat.Coprime at hcop ⊢
  rw [Nat.gcd_comm, ← Nat.gcd_rec]; exact hcop

/-- If `M` is coprime to `6`, then `2` and `3` are units modulo `M`. -/
theorem inv23_of_coprime6 {M : Nat} [NeZero M] (h6 : Nat.Coprime M 6) : Inv23 M :=
  ⟨exists_inv_res 2 (Nat.Coprime.coprime_dvd_right (by decide) h6),
   exists_inv_res 3 (Nat.Coprime.coprime_dvd_right (by decide) h6)⟩

section Affine
variable (M : Nat) [NeZero M]

abbrev Aff := Fin M × Fin M

def aApp (f : Aff M) (t : Fin M) : Fin M := f.1 * t + f.2
def aThen (f g : Aff M) : Aff M := (g.1 * f.1, g.1 * f.2 + g.2)
noncomputable def aInv (f : Aff M) : Aff M := (finv M f.1, -(finv M f.1 * f.2))

theorem aThen_app (f g : Aff M) (t : Fin M) :
    aApp M (aThen M f g) t = aApp M g (aApp M f t) := by
  unfold aApp aThen; grind

theorem aThen_assoc (f g h : Aff M) :
    aThen M (aThen M f g) h = aThen M f (aThen M g h) := by
  unfold aThen; apply Prod.ext <;> simp only <;> grind

theorem aThen_one_left (g : Aff M) : aThen M ((1 : Fin M), (0 : Fin M)) g = g := by
  unfold aThen; apply Prod.ext <;> simp only <;> grind

theorem aThen_one_right (f : Aff M) : aThen M f ((1 : Fin M), (0 : Fin M)) = f := by
  unfold aThen; apply Prod.ext <;> simp only <;> grind

theorem aInv_app (f : Aff M) (hf : IsU M f.1) (t : Fin M) :
    aApp M (aInv M f) (aApp M f t) = t := by
  have h := mul_finv M hf
  unfold aApp aInv; simp only; grind

theorem aInv_aInv (f : Aff M) (hf : IsU M f.1) : aInv M (aInv M f) = f := by
  have h := mul_finv M hf
  have e : finv M (finv M f.1) = f.1 := finv_eq_of_mul M (by grind)
  unfold aInv; simp only [e]
  apply Prod.ext <;> simp only <;> grind

theorem aInv_aThen (f g : Aff M) (hf : IsU M f.1) (hg : IsU M g.1) :
    aInv M (aThen M f g) = aThen M (aInv M g) (aInv M f) := by
  have h1 := mul_finv M hf
  have h2 := mul_finv M hg
  have e : finv M (g.1 * f.1) = finv M g.1 * finv M f.1 :=
    finv_eq_of_mul M (by calc g.1 * f.1 * (finv M g.1 * finv M f.1)
        = (g.1 * finv M g.1) * (f.1 * finv M f.1) := by grind
      _ = 1 := by rw [h1, h2]; grind)
  unfold aThen aInv; simp only [e]
  apply Prod.ext <;> simp only <;> grind

end Affine

section Walks
variable (M : Nat) [NeZero M]

theorem isU_two [Inv23 M] : IsU M (2 : Fin M) := Inv23.two

theorem isU_finv3 [Inv23 M] : IsU M (finv M (3 : Fin M)) :=
  ⟨3, by have := three_mul_finv M; grind⟩

/-- Edges of the state graph at depth `K`, labelled by affine maps. -/
inductive Edge (K : Nat) : Nat × Nat → Nat × Nat → Aff M → Prop
  | D {c f : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
      Edge K (c, f) ((2 * c) % 3 ^ (K + 1), 0) ((2 : Fin M), 0)
  | U {e : Nat} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
      Edge K (e % 3 ^ (K + 1), 0) (((e - 1) / 3) % 3 ^ (K + 1), 1)
        (finv M (3 : Fin M), -(finv M (3 : Fin M)))

/-- Walks, traversing each edge forwards (`fwd`) or backwards (`bwd`), with composed labels. -/
inductive Walk (K : Nat) : Nat × Nat → Nat × Nat → Aff M → Prop
  | nil (c : Nat × Nat) : Walk K c c (1, 0)
  | fwd {u w d : Nat × Nat} {f g : Aff M} :
      Edge M K u w f → Walk K w d g → Walk K u d (aThen M f g)
  | bwd {u w d : Nat × Nat} {f g : Aff M} :
      Edge M K u w f → Walk K u d g → Walk K w d (aThen M (aInv M f) g)

def baseState : Nat × Nat := (1, 0)

/-- The holonomy group -/
def holonomy (K : Nat) : Aff M → Prop := fun f => Walk M K baseState baseState f

theorem Walk.append {K : Nat} {u w d : Nat × Nat} {f g : Aff M}
    (h1 : Walk M K u w f) (h2 : Walk M K w d g) :
    Walk M K u d (aThen M f g) := by
  revert g
  induction h1 with
  | nil c =>
    intro g h2
    rw [aThen_one_left]
    exact h2
  | fwd he hw ih =>
    intro g h2
    have h3 := Walk.fwd he (ih h2)
    rw [aThen_assoc]
    exact h3
  | bwd he hw ih =>
    intro g h2
    have h3 := Walk.bwd he (ih h2)
    rw [aThen_assoc]
    exact h3

theorem Edge.label_isU [Inv23 M] {K : Nat} {u w : Nat × Nat} {f : Aff M}
    (h : Edge M K u w f) : IsU M f.1 := by
  cases h with
  | D hc hlt hf => exact isU_two M
  | U h1 h9 hlt => exact isU_finv3 M

theorem Edge.src_valid {K : Nat} {u w : Nat × Nat} {f : Aff M} (h : Edge M K u w f) :
    u.1 % 3 ≠ 0 ∧ u.1 < 3 ^ (K + 1) ∧ u.2 < 2 := by
  cases h with
  | D hc hlt hf => exact ⟨hc, hlt, hf⟩
  | U h1 h9 hlt =>
    exact ⟨live_mod (three_dvd_pow K) (by omega), Nat.mod_lt _ (by have := one_lt_pow3 K; omega), by omega⟩

theorem Walk.label_isU [Inv23 M] {K : Nat} {u w : Nat × Nat} {f : Aff M}
    (h : Walk M K u w f) : IsU M f.1 := by
  induction h with
  | nil c => exact ⟨1, by grind⟩
  | @fwd u w d f g he hw ih => exact isU_mul M ih (Edge.label_isU M he)
  | @bwd u w d f g he hw ih => exact isU_mul M ih (isU_finv M (Edge.label_isU M he))

theorem Walk.symm [Inv23 M] {K : Nat} {u w : Nat × Nat} {f : Aff M}
    (h : Walk M K u w f) : Walk M K w u (aInv M f) := by
  induction h with
  | nil c =>
    have e : aInv M ((1 : Fin M), (0 : Fin M)) = (1, 0) := by
      unfold aInv
      have h1 : finv M (1 : Fin M) = 1 := finv_eq_of_mul M (by grind)
      apply Prod.ext <;> simp only <;> grind
    rw [e]; exact Walk.nil c
  | @fwd u w d f g he hw ih =>
    have hf := Edge.label_isU M he
    have hg := Walk.label_isU M hw
    have key := Walk.append M ih (Walk.bwd he (Walk.nil u))
    have e : aInv M (aThen M f g)
        = aThen M (aInv M g) (aThen M (aInv M f) (1, 0)) := by
      rw [aThen_one_right, aInv_aThen M f g hf hg]
    rw [e]; exact key
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_isU M he
    have hg := Walk.label_isU M hw
    have hfi : IsU M (aInv M f).1 := isU_finv M hf
    have key := Walk.append M ih (Walk.fwd he (Walk.nil w))
    have e : aInv M (aThen M (aInv M f) g)
        = aThen M (aInv M g) (aThen M f (1, 0)) := by
      rw [aThen_one_right, aInv_aThen M (aInv M f) g hfi hg, aInv_aInv M f hf]
    rw [e]; exact key

theorem holonomy_mul {K : Nat} {f g : Aff M}
    (hf : holonomy M K f) (hg : holonomy M K g) : holonomy M K (aThen M f g) := Walk.append M hf hg

theorem holonomy_inv [Inv23 M] {K : Nat} {f : Aff M}
    (hf : holonomy M K f) : holonomy M K (aInv M f) := Walk.symm M hf

end Walks

section Fibers
variable (M : Nat) [NeZero M]

/-- The fiber of the state `(c, f)` -/
def fiber (K v c f : Nat) : Fin M → Prop :=
  fun t => ∃ n, Tree v n ∧ n % 3 ^ (K + 1) = c ∧ n % 2 = f ∧ res M n = t

/-- The image of a subset under an affine map. -/
def Img (f : Aff M) (S : Fin M → Prop) : Fin M → Prop := fun t => ∃ s, S s ∧ aApp M f s = t

theorem mul2_inj [Inv23 M] {a b : Fin M} (h : (2 : Fin M) * a = 2 * b) : a = b := by
  exact cancel_unit M (two_mul_finv M) h

theorem fiber_proj {J K v c f : Nat} (hJK : J ≤ K) {t : Fin M} (ht : fiber M K v c f t) :
    fiber M J v (c % 3 ^ (J + 1)) f t := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨n, hn, ?_, hf, hnt⟩
  rw [← hc, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega))]

theorem fiber_D_image {K v c f : Nat} {t : Fin M} (ht : fiber M K v c f t) :
    fiber M K v ((2 * c) % 3 ^ (K + 1)) 0 (2 * t) := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨2 * n, Tree.D hn, ?_, by omega, by rw [← hnt, res_mul, res_two]⟩
  subst hc
  exact (Nat.mul_mod_mod 2 n _).symm

theorem fiber_D_card_le [Inv23 M] (K v c f : Nat) :
    card (fiber M K v c f) ≤ card (fiber M K v ((2 * c) % 3 ^ (K + 1)) 0) :=
  card_le_of_inj (fun t => 2 * t) (fun _ _ h => mul2_inj M h) (fun _ ht => fiber_D_image M ht)

theorem fiber_card_iter [Inv23 M] (K v : Nat) :
    ∀ (j c : Nat), c < 3 ^ (K + 1) → c % 3 ≠ 0 →
      card (fiber M K v c 0) ≤ card (fiber M K v ((2 ^ j * c) % 3 ^ (K + 1)) 0) := by
  intro j
  induction j with
  | zero =>
    intro c hc _
    have h0 : (2 ^ 0 * c) % 3 ^ (K + 1) = c := by
      rw [Nat.pow_zero, Nat.one_mul]; exact Nat.mod_eq_of_lt hc
    rw [h0]; exact Nat.le_refl _
  | succ j ih =>
    intro c hc hc3
    have h1 := fiber_D_card_le M K v c 0
    have hd3 : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 := live_mod (three_dvd_pow K) (by omega)
    have h2 := ih ((2 * c) % 3 ^ (K + 1)) (Nat.mod_lt _ (by have := one_lt_pow3 K; omega)) hd3
    have e : (2 ^ j * ((2 * c) % 3 ^ (K + 1))) % 3 ^ (K + 1)
        = (2 ^ (j + 1) * c) % 3 ^ (K + 1) := by
      rw [Nat.mul_mod_mod, Nat.pow_succ]; congr 1; grind
    rw [e] at h2
    exact Nat.le_trans h1 h2

theorem fiber_card_const [Inv23 M] {K v c d : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) (hd : d % 3 ≠ 0) (hdl : d < 3 ^ (K + 1)) :
    card (fiber M K v c 0) = card (fiber M K v d 0) := by
  obtain ⟨j, hj⟩ := two_transitive hc hd hdl
  obtain ⟨i, hi⟩ := two_transitive hd hc hcl
  have h1 := fiber_card_iter M K v j c hcl hc
  have h2 := fiber_card_iter M K v i d hdl hd
  rw [hj] at h1
  rw [hi] at h2
  exact Nat.le_antisymm h1 h2

end Fibers

section FiberMaps
variable (M : Nat) [NeZero M]

theorem fiber_D_eq [Inv23 M] {K v c : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    ∀ t, fiber M K v ((2 * c) % 3 ^ (K + 1)) 0 t ↔ ∃ s, fiber M K v c 0 s ∧ 2 * s = t := by
  have hd : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 := live_mod (three_dvd_pow K) (by omega)
  have hlt : (2 * c) % 3 ^ (K + 1) < 3 ^ (K + 1) :=
    Nat.mod_lt _ (by have := one_lt_pow3 K; omega)
  have hcard := fiber_card_const M (v := v) hd hlt hc hcl
  have hle : card (fiber M K v ((2 * c) % 3 ^ (K + 1)) 0)
      ≤ card (fun t => ∃ s, fiber M K v c 0 s ∧ 2 * s = t) := by
    rw [hcard]
    exact card_le_of_inj (fun t => 2 * t) (fun a b h => mul2_inj M h) (fun t ht => ⟨t, ht, rfl⟩)
  intro t
  constructor
  · intro ht
    exact card_eq_of_sub (S := fun t => ∃ s, fiber M K v c 0 s ∧ 2 * s = t)
      (T := fiber M K v ((2 * c) % 3 ^ (K + 1)) 0)
      (fun t ⟨s, hs, e⟩ => by rw [← e]; exact fiber_D_image M hs) hle t ht
  · rintro ⟨s, hs, rfl⟩
    exact fiber_D_image M hs

theorem fiber_odd_sub [Inv23 M] {K v c : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    ∀ t, fiber M K v c 1 t → fiber M K v c 0 t := by
  intro t ht
  have h1 := fiber_D_image M ht
  obtain ⟨t', ht', e⟩ := (fiber_D_eq M hc hcl _).1 h1
  have : t' = t := mul2_inj M e
  rw [this] at ht'; exact ht'

/-- `t` lies in the odd fiber of `t0` exactly when `3t + 1` lies in the even fiber of `3t0 + 1` one level deeper. -/
theorem fiber_U_iff [Inv23 M] {K v t0 : Nat} (hv : v % 2 = 0)
    (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) (t : Fin M) :
    fiber M K v t0 1 t ↔
      fiber M (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0 (3 * t + 1) := by
  have hpow : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
  constructor
  · rintro ⟨n, hn, hc, hf, hnt⟩
    obtain ⟨m, hm, h6, -, hnm⟩ := tree_odd_inv hv hn hf
    have hm3 : m = 3 * n + 1 := by omega
    refine ⟨m, hm, ?_, by omega, ?_⟩
    · have hq := Nat.div_add_mod n (3 ^ (K + 1))
      rw [hc] at hq
      have e : m = (3 * t0 + 1) + 3 ^ (K + 1 + 1) * (n / 3 ^ (K + 1)) := by
        rw [hm3, hpow]; grind
      rw [e, Nat.add_mul_mod_self_left]
    · rw [hm3, res_add, res_mul, res_three, res_one, hnt]
  · rintro ⟨m, hm, hc, hf, hmt⟩
    have hdiv3 : 3 ∣ 3 ^ (K + 1 + 1) := three_dvd_pow (K + 1)
    have hdiv9 : 9 ∣ 3 ^ (K + 1 + 1) := by
      have : 3 ^ 2 ∣ 3 ^ (K + 1 + 1) := Nat.pow_dvd_pow 3 (by omega)
      simpa using this
    have hm3 : m % 3 = 1 := by
      have h := Nat.mod_mod_of_dvd m hdiv3
      rw [hc, Nat.mod_mod_of_dvd _ hdiv3] at h
      omega
    have hm9 : m % 9 = (3 * t0 + 1) % 9 := by
      have h := Nat.mod_mod_of_dvd m hdiv9
      rw [hc, Nat.mod_mod_of_dvd _ hdiv9] at h
      omega
    have h6 : m % 6 = 4 := by omega
    have h9 : ((m - 1) / 3) % 3 ≠ 0 := by omega
    obtain ⟨n, hnd⟩ : ∃ n, (m - 1) / 3 = n := ⟨_, rfl⟩
    have hn : Tree v n := by rw [← hnd]; exact Tree.U hm h6 h9
    have hm' : m = 3 * n + 1 := by omega
    refine ⟨n, hn, ?_, by omega, ?_⟩
    · obtain ⟨q, hqd⟩ : ∃ q, q = m / 3 ^ (K + 1 + 1) := ⟨_, rfl⟩
      have hq := Nat.div_add_mod m (3 ^ (K + 1 + 1))
      have hlt : 3 * t0 + 1 < 3 ^ (K + 1 + 1) := by omega
      rw [← hqd, hc, Nat.mod_eq_of_lt hlt] at hq
      have hq' : 3 ^ (K + 1 + 1) * q = 3 * (3 ^ (K + 1) * q) := by rw [hpow]; grind
      have e : n = t0 + 3 ^ (K + 1) * q := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht0l]
    · have hcm : res M m = 3 * res M n + 1 := by
        rw [hm', res_add, res_mul, res_three, res_one]
      exact cancel_unit M (three_mul_finv M) (by
        calc (3 : Fin M) * res M n = (3 * res M n + 1) - 1 := by grind
          _ = (3 * t + 1) - 1 := by rw [← hcm, hmt]
          _ = 3 * t := by grind)

/-- The common size `σ_K` of the even fibers at depth `K`. -/
noncomputable def fiberCard (K v : Nat) : Nat := card (fiber M K v 1 0)

theorem fiberCard_antitone (K v : Nat) : fiberCard M (K + 1) v ≤ fiberCard M K v := by
  unfold fiberCard
  apply card_le_of_inj (fun t => t) (fun a b h => h)
  intro t ht
  have h := fiber_proj M (Nat.le_succ K) ht
  rwa [Nat.mod_eq_of_lt (one_lt_pow3 K)] at h

theorem fiberCard_pos [Inv23 M] {v : Nat} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (K : Nat) : 1 ≤ fiberCard M K v := by
  have hlt : 1 < 3 ^ (K + 1) := one_lt_pow3 K
  have hne : fiber M K v (v % 3 ^ (K + 1)) 0 (res M v) := ⟨v, Tree.seed, rfl, hv, rfl⟩
  have hpos := card_pos hne
  have heq := fiber_card_const M (v := v) (K := K) (live_mod (three_dvd_pow K) hv3)
    (Nat.mod_lt _ (by omega)) (by omega : 1 % 3 ≠ 0) hlt
  unfold fiberCard; omega

theorem fiber_odd_card [Inv23 M] {K v t0 : Nat} (hv : v % 2 = 0)
    (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) :
    card (fiber M K v t0 1) = fiberCard M (K + 1) v := by
  have h3 := three_mul_finv M
  have hle1 : card (fiber M K v t0 1)
      ≤ card (fiber M (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0) := by
    apply card_le_of_inj (fun t => 3 * t + 1)
    · intro a b h
      exact cancel_unit M h3 (by grind)
    · intro t ht
      exact (fiber_U_iff M hv ht0 ht0l t).1 ht
  have hle2 : card (fiber M (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0)
      ≤ card (fiber M K v t0 1) := by
    apply card_le_of_inj (fun a => finv M 3 * (a - 1))
    · intro a b h
      have e : ∀ x : Fin M, 3 * (finv M 3 * (x - 1)) + 1 = x := by
        intro x
        calc 3 * (finv M 3 * (x - 1)) + 1 = (3 * finv M 3) * (x - 1) + 1 := by grind
          _ = (x - 1) + 1 := by rw [h3]; grind
          _ = x := by grind
      have : 3 * (finv M 3 * (a - 1)) + 1 = 3 * (finv M 3 * (b - 1)) + 1 := by rw [h]
      rw [e a, e b] at this; exact this
    · intro a ha
      apply (fiber_U_iff M hv ht0 ht0l _).2
      have e : 3 * (finv M 3 * (a - 1)) + 1 = a := by
        calc 3 * (finv M 3 * (a - 1)) + 1 = (3 * finv M 3) * (a - 1) + 1 := by grind
          _ = (a - 1) + 1 := by rw [h3]; grind
          _ = a := by grind
      rw [e]; exact ha
  have hc := fiber_card_const M (K := K + 1) (v := v)
    (live_mod (three_dvd_pow (K + 1)) (by omega) : ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) % 3 ≠ 0)
    (Nat.mod_lt _ (by have := one_lt_pow3 (K + 1); omega)) (by omega : 1 % 3 ≠ 0)
    (one_lt_pow3 (K + 1))
  have : card (fiber M K v t0 1) = card (fiber M (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0) :=
    Nat.le_antisymm hle1 hle2
  rw [this, hc]; rfl

end FiberMaps

section Stabilization
variable (M : Nat) [NeZero M]

theorem antitone_eventually_const : ∀ n : Nat, ∀ f : Nat → Nat, (∀ k, f (k + 1) ≤ f k) → f 0 ≤ n →
    ∃ K0, ∀ K, K0 ≤ K → f K = f K0 := by
  intro n
  induction n with
  | zero =>
    intro f hf h0
    have mono : ∀ K, f K ≤ f 0 := by
      intro K; induction K with
      | zero => exact Nat.le_refl _
      | succ K ih => exact Nat.le_trans (hf K) ih
    exact ⟨0, fun K _ => by have := mono K; omega⟩
  | succ n ih =>
    intro f hf h0
    have mono : ∀ K, f K ≤ f 0 := by
      intro K; induction K with
      | zero => exact Nat.le_refl _
      | succ K ih => exact Nat.le_trans (hf K) ih
    by_cases hall : ∀ K, f K = f 0
    · exact ⟨0, fun K _ => hall K⟩
    · have hex : ∃ K1, f K1 < f 0 := by
        apply Classical.byContradiction
        intro hno
        apply hall
        intro K
        have h1 := mono K
        have h2 : ¬ f K < f 0 := fun h => hno ⟨K, h⟩
        omega
      obtain ⟨K1, hK1⟩ := hex
      obtain ⟨K0', hK0'⟩ := ih (fun k => f (K1 + k)) (fun k => hf (K1 + k)) (by
        show f K1 ≤ n
        have := mono K1; omega)
      refine ⟨K1 + K0', fun K hK => ?_⟩
      have := hK0' (K - K1) (by omega)
      have e : K1 + (K - K1) = K := by omega
      simp only [e] at this
      exact this

/-- From depth `K0` on, odd fibers equal even fibers, and fibers do not shrink when the depth is increased. -/
def Stab (v K0 : Nat) : Prop :=
  ∀ K, K0 ≤ K →
    (∀ c, c % 3 ≠ 0 → c < 3 ^ (K + 1) → ∀ t, fiber M K v c 1 t ↔ fiber M K v c 0 t) ∧
    (∀ e, e % 3 ≠ 0 → e < 3 ^ (K + 2) →
      ∀ t, fiber M (K + 1) v e 0 t ↔ fiber M K v (e % 3 ^ (K + 1)) 0 t)

/-- The sizes `σ_K` are non-increasing, hence eventually constant. -/
theorem stabilization [Inv23 M] {v : Nat} (hv : v % 2 = 0) : ∃ K0, Stab M v K0 := by
  obtain ⟨K0, hK0⟩ := antitone_eventually_const (fiberCard M 0 v) (fun k => fiberCard M k v)
    (fun k => fiberCard_antitone M k v) (Nat.le_refl _)
  refine ⟨K0, fun K hK => ?_⟩
  have hσK := hK0 K hK
  have hσK1 := hK0 (K + 1) (by omega)
  constructor
  · intro c hc hcl t
    have c1 : card (fiber M K v c 1) = fiberCard M (K + 1) v :=
      fiber_odd_card M hv hc hcl
    have c0 : card (fiber M K v c 0) = fiberCard M K v :=
      fiber_card_const M hc hcl (by omega : 1 % 3 ≠ 0) (one_lt_pow3 K)
    have h := card_eq_of_sub (S := fiber M K v c 1) (T := fiber M K v c 0)
      (fiber_odd_sub M hc hcl) (by omega)
    exact ⟨fiber_odd_sub M hc hcl t, h t⟩
  · intro e he hel t
    have hsub : ∀ t, fiber M (K + 1) v e 0 t → fiber M K v (e % 3 ^ (K + 1)) 0 t :=
      fun t ht => fiber_proj M (Nat.le_succ K) ht
    have c1 : card (fiber M (K + 1) v e 0) = fiberCard M (K + 1) v :=
      fiber_card_const M he hel (by omega : 1 % 3 ≠ 0) (one_lt_pow3 (K + 1))
    have c0 : card (fiber M K v (e % 3 ^ (K + 1)) 0) = fiberCard M K v :=
      fiber_card_const M (live_mod (three_dvd_pow K) he)
        (Nat.mod_lt _ (by have := one_lt_pow3 K; omega)) (by omega : 1 % 3 ≠ 0) (one_lt_pow3 K)
    have h := card_eq_of_sub (S := fiber M (K + 1) v e 0)
      (T := fiber M K v (e % 3 ^ (K + 1)) 0) hsub (by omega)
    exact ⟨hsub t, h t⟩

omit [NeZero M] in
theorem Img_congr (f : Aff M) {S S' : Fin M → Prop} (h : ∀ s, S s ↔ S' s) :
    ∀ t, Img M f S t ↔ Img M f S' t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩; exact ⟨s, (h s).1 hs, e⟩
  · rintro ⟨s, hs, e⟩; exact ⟨s, (h s).2 hs, e⟩

theorem Img_aThen (f g : Aff M) (S : Fin M → Prop) :
    ∀ t, Img M (aThen M f g) S t ↔ Img M g (Img M f S) t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩
    exact ⟨aApp M f s, ⟨s, hs, rfl⟩, by rw [← aThen_app]; exact e⟩
  · rintro ⟨s', ⟨s, hs, e1⟩, e2⟩
    exact ⟨s, hs, by rw [aThen_app, e1]; exact e2⟩

theorem Img_nil (S : Fin M → Prop) : ∀ t, Img M ((1 : Fin M), (0 : Fin M)) S t ↔ S t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩
    have : aApp M ((1 : Fin M), (0 : Fin M)) s = s := by unfold aApp; simp only; grind
    rw [this] at e; rw [← e]; exact hs
  · intro h
    exact ⟨t, h, by unfold aApp; simp only; grind⟩

theorem edge_image [Inv23 M] {v K0 K : Nat} (hv : v % 2 = 0)
    (hS : Stab M v K0) (hK : K0 ≤ K) {u w : Nat × Nat} {f : Aff M}
    (h : Edge M K u w f) :
    ∀ t, Img M f (fiber M K v u.1 u.2) t ↔ fiber M K v w.1 w.2 t := by
  cases h with
  | @D c f0 hc hlt hf0 =>
    have h1 : ∀ t, fiber M K v c f0 t ↔ fiber M K v c 0 t := by
      intro t
      have hcase : f0 = 0 ∨ f0 = 1 := by omega
      rcases hcase with rfl | rfl
      · exact Iff.rfl
      · exact (hS K hK).1 c hc hlt t
    intro t
    have hfun : ∀ s : Fin M, aApp M ((2 : Fin M), (0 : Fin M)) s = 2 * s := by
      intro s; unfold aApp; simp only; grind
    refine (Img_congr M _ h1 t).trans ?_
    show (∃ s, fiber M K v c 0 s ∧ aApp M ((2 : Fin M), (0 : Fin M)) s = t) ↔
      fiber M K v ((2 * c) % 3 ^ (K + 1)) 0 t
    rw [fiber_D_eq M hc hlt t]
    constructor
    · rintro ⟨s, hs, e⟩; exact ⟨s, hs, by rw [← hfun s]; exact e⟩
    · rintro ⟨s, hs, e⟩; exact ⟨s, hs, by rw [hfun s]; exact e⟩
  | @U e h1 h9 hlt =>
    have hM : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
    have hM2 : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := hM
    have ht0 : ((e - 1) / 3) % 3 ^ (K + 1) = (e - 1) / 3 := Nat.mod_eq_of_lt (by omega)
    have hSb := (hS K hK).2 e (by omega) hlt
    have h3 := three_mul_finv M
    show ∀ t, (∃ s, fiber M K v (e % 3 ^ (K + 1)) 0 s ∧
        aApp M (finv M (3 : Fin M), -(finv M (3 : Fin M))) s = t) ↔
      fiber M K v (((e - 1) / 3) % 3 ^ (K + 1)) 1 t
    rw [ht0]
    have he0 : (3 * ((e - 1) / 3) + 1) % 3 ^ (K + 1 + 1) = e := by
      rw [show 3 * ((e - 1) / 3) + 1 = e by omega]
      exact Nat.mod_eq_of_lt (by omega)
    have hiff := fiber_U_iff M hv (K := K) (t0 := (e - 1) / 3) (by omega) (by omega)
    have key : ∀ x : Fin M, 3 * (finv M 3 * x + -finv M 3) + 1 = x := by
      intro x
      calc 3 * (finv M 3 * x + -finv M 3) + 1 = (3 * finv M 3) * x - (3 * finv M 3) + 1 := by grind
        _ = x - 1 + 1 := by rw [h3]; grind
        _ = x := by grind
    intro t
    rw [hiff t, he0]
    constructor
    · rintro ⟨s, hs, e2⟩
      have hs' := (hSb s).2 hs
      have : 3 * t + 1 = s := by
        rw [← e2]; unfold aApp; simp only; exact key s
      rw [this]; exact hs'
    · intro ha
      refine ⟨3 * t + 1, (hSb _).1 ha, ?_⟩
      unfold aApp; simp only
      calc finv M 3 * (3 * t + 1) + -finv M 3 = (finv M 3 * 3) * t + finv M 3 - finv M 3 := by grind
        _ = t := by
          have h3' : finv M 3 * 3 = 1 := by rw [Lean.Grind.CommSemiring.mul_comm]; exact h3
          rw [h3']; grind

/-- From the stabilization depth on, the label of a walk maps the fiber of its start onto the fiber of its end. -/
theorem walk_image [Inv23 M] {v K0 K : Nat} (hv : v % 2 = 0)
    (hS : Stab M v K0) (hK : K0 ≤ K) {u w : Nat × Nat} {f : Aff M}
    (h : Walk M K u w f) :
    ∀ t, Img M f (fiber M K v u.1 u.2) t ↔ fiber M K v w.1 w.2 t := by
  induction h with
  | nil c => exact Img_nil M _
  | @fwd u w d f g he hw ih =>
    have e1 := edge_image M hv hS hK he
    intro t
    refine (Img_aThen M f g _ t).trans ?_
    refine (Img_congr M g e1 t).trans ?_
    exact ih t
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_isU M he
    have e1 := edge_image M hv hS hK he
    have e2 : ∀ t, Img M (aInv M f) (fiber M K v w.1 w.2) t ↔ fiber M K v u.1 u.2 t := by
      intro t
      constructor
      · rintro ⟨s', hs', e⟩
        obtain ⟨s, hs, es⟩ := (e1 s').2 hs'
        rw [← e, ← es, aInv_app M f hf]; exact hs
      · intro ht
        exact ⟨aApp M f t, (e1 _).1 ⟨t, ht, rfl⟩, aInv_app M f hf t⟩
    intro t
    refine (Img_aThen M (aInv M f) g _ t).trans ?_
    refine (Img_congr M g e2 t).trans ?_
    exact ih t

end Stabilization

section Flat
variable (M : Nat) [NeZero M]

/-- `Φ` is compatible with every edge label. -/
def Flat (K : Nat) (Φ : Nat × Nat → Fin M) : Prop :=
  ∀ u w f, Edge M K u w f → Φ w = aApp M f (Φ u)

theorem aApp_two (x : Fin M) : aApp M ((2 : Fin M), (0 : Fin M)) x = 2 * x := by
  unfold aApp; simp only; grind

theorem flat_collapse [Inv23 M] {K : Nat} {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) {c : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) :
    Φ (c, 0) = Φ (c, 1) := by
  have h0 := hΦ _ _ _ (Edge.D (M := M) (f := 0) hc hlt (by omega))
  have h1 := hΦ _ _ _ (Edge.D (M := M) (f := 1) hc hlt (by omega))
  rw [aApp_two] at h0 h1
  exact cancel_unit M (two_mul_finv M) (by rw [← h0, ← h1])

theorem flat_double [Inv23 M] {K : Nat} {Φ : Nat × Nat → Fin M} (hΦ : Flat M K Φ)
    {c : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) :
    Φ ((2 * c) % 3 ^ (K + 1), 0) = 2 * Φ (c, 0) := by
  have h0 := hΦ _ _ _ (Edge.D (M := M) (f := 0) hc hlt (by omega))
  rw [aApp_two] at h0; exact h0

theorem flat_U [Inv23 M] {K : Nat} {Φ : Nat × Nat → Fin M} (hΦ : Flat M K Φ)
    {e : Nat} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
    3 * Φ (((e - 1) / 3) % 3 ^ (K + 1), 1) = Φ (e % 3 ^ (K + 1), 0) - 1 := by
  have he := hΦ _ _ _ (Edge.U (M := M) (K := K) (e := e) h1 h9 hlt)
  have h3 := three_mul_finv M
  unfold aApp at he; simp only at he
  rw [he]
  calc 3 * (finv M 3 * Φ (e % 3 ^ (K + 1), 0) + -finv M 3)
      = (3 * finv M 3) * Φ (e % 3 ^ (K + 1), 0) - (3 * finv M 3) := by grind
    _ = Φ (e % 3 ^ (K + 1), 0) - 1 := by rw [h3]; grind

theorem flat_one [Inv23 M] {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) : Φ (1, 0) = 1 := by
  have hM : 9 ≤ 3 ^ (K + 1) := by
    calc 9 = 3 ^ 2 := by decide
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hM2 : 3 ^ (K + 1) ≤ 3 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have u := flat_U M hΦ (e := 4) (by omega) (by omega) (by omega)
  have h4 : 4 % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  have h1m : 1 % 3 ^ (K + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hc : (4 - 1) / 3 = 1 := by decide
  rw [hc, h1m, h4] at u
  have d1 := flat_double M hΦ (c := 1) (by omega) (by omega)
  have d2 := flat_double M hΦ (c := 2) (by omega) (by omega)
  have m2 : (2 * 1) % 3 ^ (K + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  have m4 : (2 * 2) % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  rw [m2] at d1
  rw [m4] at d2
  have hcol := flat_collapse M hΦ (c := 1) (by omega) (by omega)
  rw [← hcol, d2, d1] at u
  calc Φ (1, 0) = 4 * Φ (1, 0) - 3 * Φ (1, 0) := by grind
    _ = 4 * Φ (1, 0) - (2 * (2 * Φ (1, 0)) - 1) := by rw [u]
    _ = 1 := by grind

theorem res_two_pow_unit [Inv23 M] (j : Nat) : ∃ b : Fin M, res M (2 ^ j) * b = 1 := by
  induction j with
  | zero => exact ⟨1, by rw [Nat.pow_zero, res_one]; grind⟩
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨finv M 2 * b, ?_⟩
    have h2 := two_mul_finv M
    rw [Nat.pow_succ, res_mul, res_two]
    calc res M (2 ^ j) * 2 * (finv M 2 * b) = (2 * finv M 2) * (res M (2 ^ j) * b) := by grind
      _ = 1 := by rw [h2, hb]; grind

theorem flat_hom [Inv23 M] {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) : ∀ j : Nat, Φ ((2 ^ j) % 3 ^ (K + 1), 0) = res M (2 ^ j) := by
  intro j
  induction j with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K), res_one]
    exact flat_one M hK hΦ
  | succ j ih =>
    have hc : (2 ^ j % 3 ^ (K + 1)) % 3 ≠ 0 :=
      live_mod (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt : 2 ^ j % 3 ^ (K + 1) < 3 ^ (K + 1) :=
      Nat.mod_lt _ (by have := one_lt_pow3 K; omega)
    have h1 := flat_double M hΦ hc hlt
    rw [ih] at h1
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.mul_mod_mod, e2]
    rw [e] at h1
    rw [h1, Nat.pow_succ, Nat.mul_comm, res_mul, res_two]

theorem flat_four_form [Inv23 M] {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) {c : Nat} (hc : c % 3 = 1) (hlt : c < 3 ^ (K + 1)) :
    ∃ e : Nat, (4 ^ e) % 3 ^ (K + 1) = c ∧ Φ (c, 0) = res M (4 ^ e) := by
  obtain ⟨j, hj⟩ := two_transitive (K := K) (c := 1) (d := c) (by omega) (by omega) hlt
  rw [Nat.mul_one] at hj
  have hjev : j % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one j with h0 | hodd
    · exact h0
    exfalso
    obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
    have e : 2 ^ (2 * i + 1) = 2 * 4 ^ i := by
      rw [Nat.pow_succ, Nat.pow_mul]; grind
    have hm : c % 3 = 2 ^ (2 * i + 1) % 3 := by
      rw [← hj, Nat.mod_mod_of_dvd _ (three_dvd_pow K)]
    rw [e] at hm
    have h4 := four_pow_mod_three i
    omega
  obtain ⟨e, rfl⟩ : ∃ e, j = 2 * e := ⟨j / 2, by omega⟩
  have h4e : (2 : Nat) ^ (2 * e) = 4 ^ e := by rw [Nat.pow_mul]
  refine ⟨e, by rw [← h4e]; exact hj, ?_⟩
  have hf := flat_hom M hK hΦ (2 * e)
  rw [hj, h4e] at hf
  exact hf

end Flat

section Period
variable (M : Nat) [NeZero M]

/-- `4^m = 1` in `ℤ/M`. -/
def IsPeriod (m : Nat) : Prop := res M (4 ^ m) = 1

theorem isPeriod_add {m n : Nat} (hm : IsPeriod M m) (hn : IsPeriod M n) : IsPeriod M (m + n) := by
  unfold IsPeriod at *
  rw [Nat.pow_add, res_mul, hm, hn]; grind

theorem isPeriod_mul {n : Nat} (hn : IsPeriod M n) : ∀ q, IsPeriod M (n * q) := by
  intro q
  induction q with
  | zero => unfold IsPeriod; rw [Nat.mul_zero, Nat.pow_zero, res_one]
  | succ q ih => rw [Nat.mul_succ]; exact isPeriod_add M ih hn

theorem isPeriod_cancel {m n : Nat} (hn : IsPeriod M n) (h : IsPeriod M (m + n)) : IsPeriod M m := by
  unfold IsPeriod at *
  rw [Nat.pow_add, res_mul, hn] at h
  rw [← h]; grind

theorem isPeriod_mod {m n : Nat} (hn : IsPeriod M n) (hm : IsPeriod M m) : IsPeriod M (m % n) := by
  have h := Nat.mod_add_div m n
  have h2 : IsPeriod M (m % n + n * (m / n)) := by rw [h]; exact hm
  exact isPeriod_cancel M (isPeriod_mul M hn (m / n)) h2

theorem isPeriod_gcd : ∀ m n : Nat, IsPeriod M m → IsPeriod M n → IsPeriod M (Nat.gcd m n) := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; rw [Nat.gcd_zero_left]; exact hn
  | H1 m n hm ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    exact ih (isPeriod_mod M h1 h2) h1

theorem eq_three_pow_of_dvd : ∀ n d : Nat, d ∣ 3 ^ n → ∃ b, b ≤ n ∧ d = 3 ^ b := by
  intro n
  induction n with
  | zero =>
    intro d hd
    rw [Nat.pow_zero] at hd
    exact ⟨0, Nat.le_refl _, by rw [Nat.pow_zero]; exact Nat.dvd_one.1 hd⟩
  | succ n ih =>
    intro d hd
    by_cases h3 : 3 ∣ d
    · obtain ⟨d', rfl⟩ := h3
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ n) 3] at hd
      obtain ⟨b, hb, hd'⟩ := ih d' (Nat.dvd_of_mul_dvd_mul_left (by decide) hd)
      exact ⟨b + 1, by omega, by rw [hd', Nat.pow_succ]; grind⟩
    · have hcop : Nat.Coprime d 3 := (coprime3 (c := d) (by omega)).symm
      rw [Nat.pow_succ] at hd
      obtain ⟨b, hb, hd'⟩ := ih d (Nat.Coprime.dvd_of_dvd_mul_right hcop hd)
      exact ⟨b, by omega, hd'⟩

theorem exists_min_pow3 : ∀ n : Nat, IsPeriod M (3 ^ n) →
    ∃ a, a ≤ n ∧ IsPeriod M (3 ^ a) ∧ ∀ b, b < a → ¬ IsPeriod M (3 ^ b) := by
  have key : ∀ N n : Nat, n ≤ N → IsPeriod M (3 ^ n) →
      ∃ a, a ≤ n ∧ IsPeriod M (3 ^ a) ∧ ∀ b, b < a → ¬ IsPeriod M (3 ^ b) := by
    intro N
    induction N with
    | zero =>
      intro n hn h
      have : n = 0 := by omega
      subst this
      exact ⟨0, Nat.le_refl _, h, fun b hb => by omega⟩
    | succ N ih =>
      intro n hn h
      by_cases hle : n ≤ N
      · exact ih n hle h
      · by_cases hex : ∃ b, b < n ∧ IsPeriod M (3 ^ b)
        · obtain ⟨b, hb, hQ⟩ := hex
          obtain ⟨a, ha, h1, h2⟩ := ih b (by omega) hQ
          exact ⟨a, by omega, h1, h2⟩
        · exact ⟨n, Nat.le_refl _, h, fun b hb hQ => hex ⟨b, hb, hQ⟩⟩
  intro n h
  exact key n n (Nat.le_refl _) h

theorem exists_order_pow3 {n : Nat} (h : IsPeriod M (3 ^ n)) : ∃ a, a ≤ n ∧ ∀ m, IsPeriod M m ↔ 3 ^ a ∣ m := by
  obtain ⟨a, han, hQa, hmin⟩ := exists_min_pow3 M n h
  refine ⟨a, han, fun m => ⟨fun hm => ?_, fun ⟨q, hq⟩ => ?_⟩⟩
  · have hg := isPeriod_gcd M m (3 ^ n) hm h
    obtain ⟨b, hb, hgb⟩ := eq_three_pow_of_dvd n _ (Nat.gcd_dvd_right m (3 ^ n))
    rw [hgb] at hg
    have hab : a ≤ b := by
      apply Classical.byContradiction
      intro hlt
      exact hmin b (by omega) hg
    have : 3 ^ a ∣ 3 ^ b := Nat.pow_dvd_pow 3 hab
    rw [← hgb] at this
    exact Nat.dvd_trans this (Nat.gcd_dvd_left m (3 ^ n))
  · rw [hq]; exact isPeriod_mul M hQa q

theorem three_pow_odd (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

end Period

section NoFlat
variable (M : Nat) [NeZero M]

/-- A flat assignment forces `4^(3^(K-1)) = 1` in `ℤ/M`. -/
theorem flat_four_pow [Inv23 M] {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) : res M (4 ^ (3 ^ (K - 1))) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  have hsub : n + 1 - 1 = n := by omega
  rw [hsub]
  obtain ⟨s, hs⟩ : ∃ s, s = 3 ^ n := ⟨_, rfl⟩
  rw [← hs]
  have hMs : 3 ^ (n + 1 + 1) = 9 * s := by rw [hs, Nat.pow_succ, Nat.pow_succ]; grind
  have hKs : 3 ^ (n + 1) = 3 * s := by rw [hs, Nat.pow_succ]; grind
  have h3K2 : 3 ^ (n + 1 + 2) = 27 * s := by
    rw [hs, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; grind
  have hspos : 0 < s := by rw [hs]; exact Nat.pow_pos (by decide)
  have hsodd : s % 2 = 1 := by rw [hs]; exact three_pow_odd n
  have h3 := three_mul_finv M
  have hc4 := four_pow_cong (K := n + 1) (by omega)
  rw [hsub, ← hs, hMs, hKs] at hc4
  have h4' : 4 ^ s % (9 * s) = 1 + 3 * s := by
    rw [hc4]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨y, hy⟩ : ∃ y, 2 * y + 1 = 9 * s := ⟨(9 * s - 1) / 2, by omega⟩
  have hy_lt : y < 9 * s := by omega
  have hy3 : y % 3 = 1 := by omega
  have hy9 : y % 9 = 4 := by omega
  have hcy := flat_collapse M hΦ (c := y) (by omega) (by rw [hMs]; exact hy_lt)
  have m0 : y % 3 ^ (n + 1 + 1) = y := by rw [hMs]; exact Nat.mod_eq_of_lt hy_lt
  have u1 := flat_U M hΦ (e := y + 9 * s) (by omega) (by omega) (by rw [h3K2]; omega)
  have t1 : (y + 9 * s - 1) / 3 = y := by omega
  have m1 : (y + 9 * s) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hy_lt
  rw [t1, m0, m1] at u1
  have u2 := flat_U M hΦ (e := y + 9 * s * 2) (by omega) (by omega) (by rw [h3K2]; omega)
  have t2 : (y + 9 * s * 2 - 1) / 3 = y + 3 * s := by omega
  have hy3s : y + 3 * s < 9 * s := by omega
  have m3 : (y + 3 * s) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    rw [hMs]; exact Nat.mod_eq_of_lt hy3s
  have m2 : (y + 9 * s * 2) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hy_lt
  rw [t2, m3, m2] at u2
  have hcy2 := flat_collapse M hΦ (c := y + 3 * s) (by omega) (by rw [hMs]; exact hy3s)
  rw [← hcy] at u1
  have hB : Φ (y + 3 * s, 1) = Φ (y, 0) := cancel_unit M h3 (u2.trans u1.symm)
  have hC0 : Φ (y + 3 * s, 0) = Φ (y, 0) := hcy2.trans hB
  obtain ⟨j, hj⟩ := two_transitive (K := n + 1) (c := 1) (d := y) (by omega) (by omega)
    (by rw [hMs]; exact hy_lt)
  rw [Nat.mul_one] at hj
  have hj' : 2 ^ j % (9 * s) = y := by rw [← hMs]; exact hj
  have hfy := flat_hom M (K := n + 1) (by omega) hΦ j
  rw [hj] at hfy
  have hmod : (2 ^ (j + 2 * s)) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    have e : 2 ^ (j + 2 * s) = 2 ^ j * 4 ^ s := by
      rw [Nat.pow_add, Nat.pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, y = 3 * m + 1 := ⟨y / 3, by omega⟩
    have hprod : y * (1 + 3 * s) = (y + 3 * s) + 9 * s * m := by
      rw [hm]; grind
    rw [hMs, e, Nat.mul_mod, hj', h4', hprod, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hy3s
  have hf2 := flat_hom M (K := n + 1) (by omega) hΦ (j + 2 * s)
  rw [hmod] at hf2
  have hpow : res M (2 ^ (j + 2 * s)) = res M (2 ^ j) := hf2.symm.trans (hC0.trans hfy)
  obtain ⟨b, hb⟩ := res_two_pow_unit M j
  have h2 : res M (2 ^ j) * res M (2 ^ (2 * s)) = res M (2 ^ j) * 1 := by
    rw [← res_mul, ← Nat.pow_add]
    rw [hpow]; grind
  have h2' := cancel_unit M hb h2
  have e4 : 4 ^ s = 2 ^ (2 * s) := by rw [Nat.pow_mul]
  rw [e4]; exact h2'

/-- If `4^(3^(K-1)) = 1` in `ℤ/M`, a flat assignment leads to a contradiction. -/
theorem flat_contra [Inv23 M] (hM : 1 < M) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin M}
    (hΦ : Flat M K Φ) (h4 : res M (4 ^ (3 ^ (K - 1))) = 1) : False := by
  have h3 := three_mul_finv M
  obtain ⟨a, haK, hk⟩ := exists_order_pow3 M (n := K - 1) h4
  have hk' : ∀ m, res M (4 ^ m) = 1 ↔ 3 ^ a ∣ m := hk
  have ha1 : 1 ≤ a := by
    apply Classical.byContradiction
    intro h0
    have ha0 : a = 0 := by omega
    subst ha0
    have h1 : res M (4 ^ 1) = 1 := (hk' 1).2 (by simp)
    rw [Nat.pow_one] at h1
    have h30 : (3 : Fin M) = 0 := by
      have e : res M 4 = 3 + 1 := res_add M 3 1
      rw [e] at h1; grind
    exact three_ne_zero M hM h30
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, r = 3 ^ a' := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = 3 ^ K := ⟨_, rfl⟩
  have hq2 : 3 ^ (a' + 1 + 1) = 9 * r := by rw [hr, Nat.pow_succ, Nat.pow_succ]; grind
  have hrpos : 0 < r := by rw [hr]; exact Nat.pow_pos (by decide)
  have hle : 3 ^ (a' + 1 + 1) ≤ 3 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hq2, ← hR] at hle
  have hR3 : 3 ≤ R := by
    rw [hR]
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ k + 1))
  have hM : 3 ^ (K + 1) = 3 * R := by rw [hR, Nat.pow_succ]; grind
  have hM2 : 3 ^ (K + 2) = 9 * R := by rw [hR, Nat.pow_succ, Nat.pow_succ]; grind
  have hdv : 3 ^ (a' + 1 + 1) ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega)
  have hcop4 : Nat.Coprime (3 ^ (a' + 1 + 1)) 4 :=
    Nat.Coprime.pow_left (a' + 1 + 1) (by decide : Nat.Coprime 3 4)
  have hc2lt : 4 + 9 * r < 3 ^ (K + 1) := by rw [hM]; omega
  obtain ⟨e, he, hΦe⟩ := flat_four_form M hK hΦ (c := 4 + 9 * r) (by omega) hc2lt
  have he1 : 1 ≤ e := by
    apply Classical.byContradiction
    intro h0
    have he0 : e = 0 := by omega
    rw [he0, Nat.pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)] at he
    omega
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hm1 : 4 ^ (e' + 1) % 3 ^ (a' + 1 + 1) = (4 + 9 * r) % 3 ^ (a' + 1 + 1) := by
    have := Nat.mod_mod_of_dvd (4 ^ (e' + 1)) hdv
    rw [he] at this; exact this.symm
  have hm2 : 4 ^ (e' + 1) % 3 ^ (a' + 1 + 1) = 4 := by
    rw [hm1, hq2, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  have hpow4 : 4 ^ (e' + 1) = 4 * 4 ^ e' := by rw [Nat.pow_succ, Nat.mul_comm]
  have hm3 : (4 * 4 ^ e') % 3 ^ (a' + 1 + 1) = (4 * 1) % 3 ^ (a' + 1 + 1) := by
    rw [← hpow4, hm2, hq2]; rw [Nat.mod_eq_of_lt (by omega)]
  have hm4 := mod_cancel_mul_left hcop4 (Nat.pow_pos (by decide) : 1 ≤ 4 ^ e') hm3
  have hd1 : 3 ^ (a' + 1) ∣ e' :=
    (four_pow_mod_eq_one_iff (K := a' + 1) (m := e')).1 (by
      rw [hm4, hq2]; exact Nat.mod_eq_of_lt (by omega))
  have hφ2 : Φ (4 + 9 * r, 0) = 4 := by
    rw [hΦe, Nat.pow_succ, res_mul, (hk' e').2 hd1, res_four]; grind
  have ub := flat_U M hΦ (e := 4 + 9 * r) (by omega) (by omega) (by rw [hM2]; omega)
  have tb : (4 + 9 * r - 1) / 3 = 1 + 3 * r := by omega
  have mb1 : (1 + 3 * r) % 3 ^ (K + 1) = 1 + 3 * r := Nat.mod_eq_of_lt (by rw [hM]; omega)
  have mb2 : (4 + 9 * r) % 3 ^ (K + 1) = 4 + 9 * r := Nat.mod_eq_of_lt hc2lt
  rw [tb, mb1, mb2, hφ2] at ub
  have hΦ1 : Φ (1 + 3 * r, 1) = 1 := cancel_unit M h3 (by rw [ub]; grind)
  have hcol := flat_collapse M hΦ (c := 1 + 3 * r) (by omega) (by rw [hM]; omega)
  have hone : Φ (1 + 3 * r, 0) = 1 := hcol.trans hΦ1
  obtain ⟨d, hd, hΦd⟩ := flat_four_form M hK hΦ (c := 1 + 3 * r) (by omega) (by rw [hM]; omega)
  have hpd : res M (4 ^ d) = 1 := hΦd.symm.trans hone
  have hdd : 3 ^ (a' + 1) ∣ d := (hk' d).1 hpd
  have hmodd : 4 ^ d % 3 ^ (a' + 1 + 1) = 1 := (four_pow_mod_eq_one_iff (K := a' + 1) (m := d)).2 hdd
  have h5 := Nat.mod_mod_of_dvd (4 ^ d) hdv
  rw [hd] at h5
  rw [hq2] at h5 hmodd
  rw [Nat.mod_eq_of_lt (by omega : 1 + 3 * r < 9 * r)] at h5
  omega

/-- For `M > 1` with `2, 3` invertible there is no flat assignment at any depth `K ≥ 1`. -/
theorem no_flat [Inv23 M] (hM : 1 < M) {K : Nat} (hK : 1 ≤ K) :
    ¬ ∃ Φ : Nat × Nat → Fin M, Flat M K Φ := by
  rintro ⟨Φ, hΦ⟩
  exact flat_contra M hM hK hΦ (flat_four_pow M hK hΦ)

end NoFlat

section Connected
variable (M : Nat) [NeZero M]

theorem walk_two_pow {K : Nat} :
    ∀ j : Nat, ∃ g : Aff M, Walk M K baseState ((2 ^ j) % 3 ^ (K + 1), 0) g := by
  intro j
  induction j with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)]
    exact ⟨_, Walk.nil baseState⟩
  | succ j ih =>
    obtain ⟨g, hg⟩ := ih
    have hc := live_mod (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt := Nat.mod_lt (2 ^ j) (show 0 < 3 ^ (K + 1) by have := one_lt_pow3 K; omega)
    have he := Edge.D (M := M) (K := K) (f := 0) hc hlt (by omega)
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.mul_mod_mod, e2]
    rw [e] at he
    exact ⟨_, Walk.append M hg (Walk.fwd he (Walk.nil _))⟩

theorem connected_even {K : Nat} {c : Nat} (hc : c % 3 ≠ 0)
    (hlt : c < 3 ^ (K + 1)) : ∃ g : Aff M, Walk M K baseState (c, 0) g := by
  obtain ⟨j, hj⟩ := two_transitive (K := K) (c := 1) (d := c) (by omega) hc hlt
  rw [Nat.mul_one] at hj
  obtain ⟨g, hg⟩ := walk_two_pow M (K := K) j
  rw [hj] at hg
  exact ⟨g, hg⟩

/-- Every state is reached from `(1, 0)` by a walk. -/
theorem connected {K : Nat} {c f : Nat}
    (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
    ∃ g : Aff M, Walk M K baseState (c, f) g := by
  have hcase : f = 0 ∨ f = 1 := by omega
  rcases hcase with rfl | rfl
  · exact connected_even M hc hlt
  · have hM : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
    have h1 : (3 * c + 1) % 3 = 1 := by omega
    have h9 : (3 * c + 1) % 9 ≠ 1 := by omega
    have hlt2 : 3 * c + 1 < 3 ^ (K + 2) := by omega
    have he := Edge.U (M := M) (K := K) (e := 3 * c + 1) h1 h9 hlt2
    have h3c : (3 * c + 1 - 1) / 3 = c := by omega
    rw [h3c, Nat.mod_eq_of_lt hlt] at he
    have hsrc : (3 * c + 1) % 3 ^ (K + 1) % 3 ≠ 0 :=
      live_mod (three_dvd_pow K) (by omega)
    obtain ⟨g, hg⟩ := connected_even M hsrc
      (Nat.mod_lt _ (by have := one_lt_pow3 K; omega))
    exact ⟨_, Walk.append M hg (Walk.fwd he (Walk.nil _))⟩

open Classical in
/-- A common fixed point of the holonomy group gives a flat assignment. -/
theorem flat_of_fixed [Inv23 M] {K : Nat} (x : Fin M)
    (hx : ∀ f, holonomy M K f → aApp M f x = x) : ∃ Φ : Nat × Nat → Fin M, Flat M K Φ := by
  have hval : ∀ {u : Nat × Nat} {g1 g2 : Aff M}, Walk M K baseState u g1 → Walk M K baseState u g2 →
      aApp M g1 x = aApp M g2 x := by
    intro u g1 g2 h1 h2
    have hh : holonomy M K (aThen M g1 (aInv M g2)) := Walk.append M h1 (Walk.symm M h2)
    have hfix := hx _ hh
    rw [aThen_app] at hfix
    have hu := Walk.label_isU M h2
    have hinv : ∀ z, aApp M g2 (aApp M (aInv M g2) z) = z := by
      intro z
      have hi : IsU M (aInv M g2).1 := isU_finv M hu
      have := aInv_app M (aInv M g2) hi z
      rwa [aInv_aInv M g2 hu] at this
    have := congrArg (aApp M g2) hfix
    rw [hinv] at this
    exact this
  refine ⟨fun u => if h : ∃ g, Walk M K baseState u g then aApp M h.choose x else 0, ?_⟩
  rintro ⟨c, f0⟩ w f he
  obtain ⟨hc, hlt, hf⟩ := Edge.src_valid M he
  obtain ⟨g, hg⟩ := connected M hc hlt hf
  have hu : ∃ g, Walk M K baseState (c, f0) g := ⟨g, hg⟩
  have hw : ∃ g', Walk M K baseState w g' :=
    ⟨_, Walk.append M hg (Walk.fwd he (Walk.nil w))⟩
  show (if h : ∃ g, Walk M K baseState w g then aApp M h.choose x else 0) =
    aApp M f (if h : ∃ g, Walk M K baseState (c, f0) g then aApp M h.choose x else 0)
  rw [dite_eq_left_of_eq_true (eq_true hw), dite_eq_left_of_eq_true (eq_true hu)]
  have e1 := hval hw.choose_spec (Walk.append M hg (Walk.fwd he (Walk.nil w)))
  have e2 := hval hu.choose_spec hg
  rw [e1, e2, aThen_app, aThen_app]
  simp only [aApp]; grind

end Connected

section Translations
variable (M : Nat) [NeZero M]

theorem translation_add [Inv23 M] {K : Nat} {d₁ d₂ : Fin M}
    (h₁ : holonomy M K ((1 : Fin M), d₁)) (h₂ : holonomy M K ((1 : Fin M), d₂)) :
    holonomy M K ((1 : Fin M), d₁ + d₂) := by
  have := holonomy_mul M h₁ h₂
  have e : aThen M ((1 : Fin M), d₁) ((1 : Fin M), d₂) = ((1 : Fin M), d₁ + d₂) := by
    unfold aThen; apply Prod.ext <;> simp only <;> grind
  rwa [e] at this

theorem translation_neg [Inv23 M] {K : Nat} {d : Fin M}
    (h : holonomy M K ((1 : Fin M), d)) : holonomy M K ((1 : Fin M), -d) := by
  have := holonomy_inv M h
  have h1 : finv M (1 : Fin M) = 1 := finv_eq_of_mul M (by grind)
  have e : aInv M ((1 : Fin M), d) = ((1 : Fin M), -d) := by
    unfold aInv; simp only [h1]; apply Prod.ext <;> simp only <;> grind
  rwa [e] at this

theorem translation_nsmul [Inv23 M] {K : Nat} {d : Fin M}
    (h : holonomy M K ((1 : Fin M), d)) : ∀ k : Nat, holonomy M K ((1 : Fin M), res M k * d) := by
  intro k
  induction k with
  | zero =>
    have : res M 0 * d = 0 := by rw [res_zero]; grind
    rw [this]; exact Walk.nil baseState
  | succ k ih =>
    have e : res M (k + 1) * d = res M k * d + d := by rw [res_add, res_one]; grind
    rw [e]; exact translation_add M ih h

end Translations


section Loop
variable (M : Nat) [NeZero M]

theorem w0_walk [Inv23 M] (K : Nat) (hK : 1 ≤ K) :
    Walk M K baseState baseState
      (aThen M ((2 : Fin M), 0) (aThen M ((2 : Fin M), 0)
        (aThen M (finv M (3 : Fin M), -finv M (3 : Fin M))
          (aThen M ((2 : Fin M), 0) (aThen M (aInv M ((2 : Fin M), 0)) ((1 : Fin M), 0)))))) := by
  have h9 : 9 ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ K + 1)
  have h27 : 3 ^ (K + 1) ≤ 3 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have m1 : (2 * 1) % 3 ^ (K + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  have m2 : (2 * 2) % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  have m4 : 4 % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  have mt : ((4 - 1) / 3) % 3 ^ (K + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have e1 : Edge M K (1, 0) (2, 0) ((2 : Fin M), 0) := by
    have h := Edge.D (M := M) (K := K) (c := 1) (f := 0) (by decide) (by omega) (by decide)
    rwa [m1] at h
  have e2 : Edge M K (2, 0) (4, 0) ((2 : Fin M), 0) := by
    have h := Edge.D (M := M) (K := K) (c := 2) (f := 0) (by decide) (by omega) (by decide)
    rwa [m2] at h
  have e3 : Edge M K (4, 0) (1, 1) (finv M (3 : Fin M), -finv M (3 : Fin M)) := by
    have h := Edge.U (M := M) (K := K) (e := 4) (by decide) (by decide) (by omega)
    rwa [m4, mt] at h
  have e4 : Edge M K (1, 1) (2, 0) ((2 : Fin M), 0) := by
    have h := Edge.D (M := M) (K := K) (c := 1) (f := 1) (by decide) (by omega) (by decide)
    rwa [m1] at h
  exact Walk.fwd e1 (Walk.fwd e2 (Walk.fwd e3 (Walk.fwd e4 (Walk.bwd e1 (Walk.nil _)))))

theorem w0_label [Inv23 M] :
    aThen M ((2 : Fin M), 0) (aThen M ((2 : Fin M), 0)
        (aThen M (finv M (3 : Fin M), -finv M (3 : Fin M))
          (aThen M ((2 : Fin M), 0) (aThen M (aInv M ((2 : Fin M), 0)) ((1 : Fin M), 0)))))
      = (4 * finv M (3 : Fin M), -finv M (3 : Fin M)) := by
  have h2 := two_mul_finv M
  have h3 := three_mul_finv M
  unfold aThen aInv
  generalize finv M (2 : Fin M) = i2 at *
  generalize finv M (3 : Fin M) = i3 at *
  apply Prod.ext <;> simp only <;> grind

theorem w0_mem [Inv23 M] (K : Nat) (hK : 1 ≤ K) :
    holonomy M K (4 * finv M (3 : Fin M), -finv M (3 : Fin M)) := by
  have := w0_walk M K hK
  rwa [w0_label M] at this

/-- For `k = (ℓ, m)` in the holonomy group, the commutator `k w₀ k⁻¹ w₀⁻¹` is a translation `t ↦ t + τ`, and… -/
theorem commutator_translation [Inv23 M] (K : Nat) (hK : 1 ≤ K) {k : Aff M}
    (hk : holonomy M K k) :
    ∃ τ : Fin M, holonomy M K ((1 : Fin M), τ) ∧ aApp M k 1 = 1 + 4 * k.1 * τ := by
  have hw := w0_mem M K hK
  have hs : IsU M (4 * finv M (3 : Fin M)) := Walk.label_isU M hw
  have hl : IsU M k.1 := Walk.label_isU M hk
  have hg := holonomy_mul M (holonomy_mul M (holonomy_mul M hk hw) (holonomy_inv M hk))
    (holonomy_inv M hw)
  have h3 := three_mul_finv M
  obtain ⟨l, m⟩ := k
  have hil := mul_finv M hl
  have his := mul_finv M hs
  unfold aThen aInv at hg
  simp only at hg hil his ⊢
  generalize finv M l = il at *
  generalize finv M (4 * finv M (3 : Fin M)) = is at *
  generalize finv M (3 : Fin M) = i3 at *
  have e1 : is * (il * (4 * i3 * l)) = 1 := by grind
  rw [e1] at hg
  refine ⟨_, hg, ?_⟩
  unfold aApp
  simp only
  grind

end Loop

section Reduce
variable (M q : Nat) [NeZero M] [NeZero q]

/-- Reduction `ℤ/M → ℤ/q`. -/
def red (a : Fin M) : Fin q := res q a.val

def redAff (f : Aff M) : Aff q := (red M q f.1, red M q f.2)

variable {M q}

omit [NeZero M] in
theorem red_add (hq : q ∣ M) (a b : Fin M) : red M q (a + b) = red M q a + red M q b := by
  unfold red
  rw [← res_add]
  apply (res_eq_iff q _ _).2
  rw [Fin.val_add, Nat.mod_mod_of_dvd _ hq]

omit [NeZero M] in
theorem red_mul (hq : q ∣ M) (a b : Fin M) : red M q (a * b) = red M q a * red M q b := by
  unfold red
  rw [← res_mul]
  apply (res_eq_iff q _ _).2
  rw [Fin.val_mul, Nat.mod_mod_of_dvd _ hq]

theorem red_res (hq : q ∣ M) (n : Nat) : red M q (res M n) = res q n := by
  unfold red
  rw [res_val]
  exact (res_eq_iff q _ _).2 (Nat.mod_mod_of_dvd n hq)

theorem red_zero (hq : q ∣ M) : red M q (0 : Fin M) = 0 := red_res hq 0
theorem red_one (hq : q ∣ M) : red M q (1 : Fin M) = 1 := red_res hq 1
theorem red_two (hq : q ∣ M) : red M q (2 : Fin M) = 2 := red_res hq 2
theorem red_three (hq : q ∣ M) : red M q (3 : Fin M) = 3 := red_res hq 3

theorem red_neg (hq : q ∣ M) (a : Fin M) : red M q (-a) = - red M q a := by
  have h := red_add hq a (-a)
  rw [show a + -a = 0 by grind, red_zero hq] at h
  grind

theorem red_finv (hq : q ∣ M) {a : Fin M} (ha : IsU M a) :
    red M q (finv M a) = finv q (red M q a) := by
  have h := mul_finv M ha
  have h2 := congrArg (red M q) h
  rw [red_mul hq, red_one hq] at h2
  exact (finv_eq_of_mul q (a := red M q a) (b := red M q (finv M a)) h2).symm

omit [NeZero M] in
theorem redAff_aThen (hq : q ∣ M) (f g : Aff M) :
    redAff M q (aThen M f g) = aThen q (redAff M q f) (redAff M q g) := by
  unfold redAff aThen
  simp only [red_add hq, red_mul hq]

theorem redAff_aInv (hq : q ∣ M) (f : Aff M) (hf : IsU M f.1) :
    redAff M q (aInv M f) = aInv q (redAff M q f) := by
  unfold redAff aInv
  simp only [red_neg hq, red_mul hq, red_finv hq hf]

theorem redAff_one (hq : q ∣ M) :
    redAff M q ((1 : Fin M), (0 : Fin M)) = ((1 : Fin q), (0 : Fin q)) := by
  unfold redAff; simp only [red_one hq, red_zero hq]

/-- The state graph does not depend on the modulus, so every edge modulo `q` is the reduction of the same edge… -/
theorem Edge.lift [Inv23 M] [Inv23 q] (hq : q ∣ M) {K : Nat} {u w : Nat × Nat}
    {f : Aff q} (h : Edge q K u w f) : ∃ g : Aff M, Edge M K u w g ∧ redAff M q g = f := by
  cases h with
  | D hc hlt hf =>
    refine ⟨((2 : Fin M), 0), Edge.D hc hlt hf, ?_⟩
    unfold redAff; simp only [red_two hq, red_zero hq]
  | U h1 h9 hlt =>
    refine ⟨(finv M (3 : Fin M), -finv M (3 : Fin M)), Edge.U h1 h9 hlt, ?_⟩
    have hu : IsU M (3 : Fin M) := Inv23.three
    unfold redAff; simp only [red_neg hq, red_finv hq hu, red_three hq]

theorem Walk.lift [Inv23 M] [Inv23 q] (hq : q ∣ M) {K : Nat} {u w : Nat × Nat}
    {f : Aff q} (h : Walk q K u w f) : ∃ g : Aff M, Walk M K u w g ∧ redAff M q g = f := by
  induction h with
  | nil c => exact ⟨_, Walk.nil c, redAff_one hq⟩
  | @fwd u w d f g he hw ih =>
    obtain ⟨gf, hef, hrf⟩ := Edge.lift hq he
    obtain ⟨gg, hwg, hrg⟩ := ih
    exact ⟨aThen M gf gg, Walk.fwd hef hwg, by rw [redAff_aThen hq, hrf, hrg]⟩
  | @bwd u w d f g he hw ih =>
    obtain ⟨gf, hef, hrf⟩ := Edge.lift hq he
    obtain ⟨gg, hwg, hrg⟩ := ih
    refine ⟨aThen M (aInv M gf) gg, Walk.bwd hef hwg, ?_⟩
    rw [redAff_aThen hq, redAff_aInv hq gf (Edge.label_isU M hef), hrf, hrg]

end Reduce

section TranslationOne
variable (M : Nat) [NeZero M]

theorem res_val_self (e : Fin M) : res M e.val = e := by
  apply Fin.ext; rw [res_val, Nat.mod_eq_of_lt e.isLt]

theorem res_self : res M M = 0 := by
  rw [← res_zero M]; apply (res_eq_iff M _ _).2; simp

theorem exists_least (P : Nat → Prop) : (∃ n, P n) → ∃ n, P n ∧ ∀ r, r < n → ¬ P r := by
  rintro ⟨n, hn⟩
  revert hn
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases h : ∀ r, r < n → ¬ P r
    · exact ⟨n, hn, h⟩
    · obtain ⟨r, hr, hPr⟩ : ∃ r, r < n ∧ P r := by
        apply Classical.byContradiction
        intro hh
        apply h
        intro r hr hp
        exact hh ⟨r, hr, hp⟩
      exact ih r hr hPr

/-- For `M` coprime to `6` and `K ≥ 1`, the translation `t ↦ t + 1` lies in the holonomy group. -/
theorem translation_one (h6 : Nat.Coprime M 6) {K : Nat} (hK : 1 ≤ K) :
    holonomy M K ((1 : Fin M), 1) := by
  haveI := inv23_of_coprime6 h6
  have hM0 : holonomy M K ((1 : Fin M), res M M) := by
    rw [res_self]; exact Walk.nil baseState
  obtain ⟨q, ⟨hq0, hqT⟩, hmin⟩ :=
    exists_least (fun n => 0 < n ∧ holonomy M K ((1 : Fin M), res M n))
      ⟨M, Nat.pos_of_ne_zero (NeZero.ne M), hM0⟩
  have hdvd : ∀ x : Nat, holonomy M K ((1 : Fin M), res M x) → q ∣ x := by
    intro x hx
    have h1 := translation_add M hx (translation_neg M (translation_nsmul M hqT (x / q)))
    have h2 : res M x = res M q * res M (x / q) + res M (x % q) := by
      rw [← res_mul, ← res_add, Nat.div_add_mod]
    have h4 : res M x + -(res M (x / q) * res M q) = res M (x % q) := by
      rw [h2]; grind
    rw [h4] at h1
    apply Nat.dvd_of_mod_eq_zero
    apply Classical.byContradiction
    intro hz
    exact hmin _ (Nat.mod_lt x hq0) ⟨by omega, h1⟩
  by_cases hq1 : q = 1
  · subst hq1; exact hqT
  exfalso
  have hqM : q ∣ M := hdvd M hM0
  haveI : NeZero q := ⟨by omega⟩
  haveI := inv23_of_coprime6 (Nat.Coprime.coprime_dvd_left hqM h6)
  have hx : ∀ f : Aff q, holonomy q K f → aApp q f 1 = 1 := by
    intro f hf
    obtain ⟨g, hg, hrg⟩ := Walk.lift hqM hf
    obtain ⟨τ, hτ, hv⟩ := commutator_translation M K hK hg
    have hrτ : red M q τ = 0 := by
      unfold red
      rw [← res_zero q]
      apply (res_eq_iff q _ _).2
      rw [Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd (hdvd τ.val (by rw [res_val_self]; exact hτ))
    have h1 : red M q (aApp M g 1) = 1 := by
      rw [hv, red_add hqM, red_one hqM, red_mul hqM, hrτ]; grind
    have h2 : red M q (aApp M g 1) = aApp q (redAff M q g) 1 := by
      unfold aApp redAff
      simp only [red_add hqM, red_mul hqM, red_one hqM]
    rw [← hrg, ← h2]; exact h1
  obtain ⟨Φ, hΦ⟩ := flat_of_fixed q 1 hx
  exact no_flat q (by omega) hK ⟨Φ, hΦ⟩

end TranslationOne

theorem exists_of_card_pos {M : Nat} {S : Fin M → Prop} (h : 1 ≤ card S) : ∃ t, S t := by
  classical
  unfold card at h
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos h
  exact ⟨t, (mem_cardlist).1 ht⟩

section Density
variable (M : Nat) [NeZero M]

/-- For `M` coprime to `6`, an even seed `v` with `3 ∤ v`, and a live class `c` modulo -/
theorem fiber_full (h6 : Nat.Coprime M 6) {v : Nat} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    {J c : Nat} (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (J + 1)) : ∀ r : Fin M, fiber M J v c 0 r := by
  haveI := inv23_of_coprime6 h6
  obtain ⟨K0, hS⟩ := stabilization M hv
  obtain ⟨K, hKdef⟩ : ∃ K, K = max (max K0 J) 1 := ⟨_, rfl⟩
  have hKK0 : K0 ≤ K := by omega
  have hKJ : J ≤ K := by omega
  have himg := walk_image M hv hS hKK0 (translation_one M h6 (K := K) (by omega))
  obtain ⟨t0, ht0⟩ := exists_of_card_pos (S := fiber M K v 1 0) (fiberCard_pos M hv hv3 K)
  have step : ∀ t, fiber M K v 1 0 t → fiber M K v 1 0 (t + 1) := fun t ht =>
    (himg (t + 1)).1 ⟨t, ht, by unfold aApp; simp only; grind⟩
  have key : ∀ k : Nat, fiber M K v 1 0 (t0 + res M k) := by
    intro k
    induction k with
    | zero => rw [res_zero, show t0 + (0 : Fin M) = t0 by grind]; exact ht0
    | succ k ih => rw [res_add, res_one, ← Lean.Grind.Semiring.add_assoc]; exact step _ ih
  have hfull : ∀ r' : Fin M, fiber M K v 1 0 r' := by
    intro r'
    have := key (r' - t0).val
    rwa [res_val_self, show t0 + (r' - t0) = r' by grind] at this
  have hcK : c < 3 ^ (K + 1) :=
    Nat.lt_of_lt_of_le hcl (Nat.pow_le_pow_right (by decide) (by omega))
  have hfullc : ∀ t, fiber M K v c 0 t := by
    have hcc := fiber_card_const M (v := v) (K := K) (c := 1) (d := c)
      (by omega) (one_lt_pow3 K) hc hcK
    have hu : card (fiber M K v 1 0) = card (fun _ : Fin M => True) :=
      card_congr (fun t => ⟨fun _ => trivial, fun _ => hfull t⟩)
    have := card_eq_of_sub (S := fiber M K v c 0) (T := fun _ : Fin M => True)
      (fun _ _ => trivial) (by omega)
    exact fun t => this t trivial
  intro r
  have hr := fiber_proj M hKJ (hfullc r)
  rwa [Nat.mod_eq_of_lt hcl] at hr

end Density


/-- The shortcut map `n ↦ n/2` or `(3n + 1)/2`. -/
def shortcut (n : Nat) : Nat := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The number of odd terms among `n, shortcut n, …, shortcut^[a-1] n`. -/
def oddCount : Nat → Nat → Nat
  | 0, _ => 0
  | a + 1, r => r % 2 + oddCount a (shortcut r)

theorem reaches_shortcut (n : Nat) : Reaches (shortcut n) n := by
  by_cases h : n % 2 = 0
  · exact ⟨1, by simp [iter, shortcut, collatz, h]⟩
  · refine ⟨2, ?_⟩
    show collatz (collatz n) = shortcut n
    unfold shortcut collatz
    split <;> split <;> omega

theorem reaches_iter_shortcut : ∀ (a n : Nat), Reaches (iter shortcut a n) n := by
  intro a
  induction a with
  | zero => intro n; exact ⟨0, rfl⟩
  | succ a ih => intro n; exact reaches_trans (reaches_shortcut n) (ih (shortcut n))

theorem shortcut_step (a r t : Nat) :
    shortcut (r + 2 ^ (a + 1) * t) = shortcut r + 2 ^ a * (3 ^ (r % 2) * t) := by
  have h2 : 2 ^ (a + 1) * t = 2 * (2 ^ a * t) := by rw [Nat.pow_succ]; grind
  have h3 : 2 ^ a * (3 ^ (r % 2) * t) = 3 ^ (r % 2) * (2 ^ a * t) := by grind
  rw [h2, h3]
  generalize 2 ^ a * t = k
  by_cases h : r % 2 = 0
  · rw [h, Nat.pow_zero, Nat.one_mul]
    unfold shortcut
    split <;> omega
  · have h1 : r % 2 = 1 := by omega
    rw [h1, Nat.pow_one]
    unfold shortcut
    split <;> omega

/-- `shortcut^[a] (r + 2^a t) = shortcut^[a] r + 3^j t`, where `j` counts the odd steps. -/
theorem parity_prefix : ∀ a r t : Nat,
    iter shortcut a (r + 2 ^ a * t) = iter shortcut a r + 3 ^ oddCount a r * t := by
  intro a
  induction a with
  | zero => intro r t; simp [iter, oddCount]
  | succ a ih =>
    intro r t
    show iter shortcut a (shortcut (r + 2 ^ (a + 1) * t)) = iter shortcut a (shortcut r) + 3 ^ oddCount (a + 1) r * t
    rw [shortcut_step, ih, oddCount, Nat.pow_add]
    grind

theorem shortcut_live (x : Nat) (h : x % 3 ≠ 0) : shortcut x % 3 ≠ 0 := by
  unfold shortcut; split <;> omega

theorem shortcut_odd_live (x : Nat) (h : x % 2 = 1) : shortcut x % 3 ≠ 0 := by
  unfold shortcut
  have : x % 2 ≠ 0 := by omega
  simp only [this, ite_false]; omega

theorem iter_live : ∀ a x : Nat, x % 3 ≠ 0 → iter shortcut a x % 3 ≠ 0 := by
  intro a
  induction a with
  | zero => intro x h; exact h
  | succ a ih => intro x h; exact ih (shortcut x) (shortcut_live x h)

/-- After at least one odd step the shortcut orbit is not divisible by `3`. -/
theorem live_after_odd : ∀ a r : Nat, 1 ≤ oddCount a r → iter shortcut a r % 3 ≠ 0 := by
  intro a
  induction a with
  | zero => intro r h; simp [oddCount] at h
  | succ a ih =>
    intro r h
    by_cases h1 : 1 ≤ oddCount a (shortcut r)
    · exact ih (shortcut r) h1
    · have h0 : oddCount a (shortcut r) = 0 := by omega
      have hr : r % 2 = 1 := by
        have : oddCount (a + 1) r = r % 2 + oddCount a (shortcut r) := rfl
        omega
      exact iter_live a (shortcut r) (shortcut_odd_live r hr)

theorem oddCount_succ_right : ∀ a x : Nat, oddCount (a + 1) x = oddCount a x + iter shortcut a x % 2 := by
  intro a
  induction a with
  | zero => intro x; simp [oddCount, iter]
  | succ a ih =>
    intro x
    show x % 2 + oddCount (a + 1) (shortcut x) = (x % 2 + oddCount a (shortcut x)) + iter shortcut a (shortcut x) % 2
    rw [ih]; omega

/-- Every class modulo `2^a` contains `r'` whose prefix of some length `a' ≥ a` has an odd step. -/
theorem exists_odd_prefix (a r : Nat) :
    ∃ a' r', a ≤ a' ∧ r' % 2 ^ a = r % 2 ^ a ∧ 1 ≤ oddCount a' r' := by
  have hodd := three_pow_odd (oddCount a (r % 2 ^ a))
  by_cases h : iter shortcut a (r % 2 ^ a) % 2 = 1
  · refine ⟨a + 1, r % 2 ^ a + 2 ^ a * 0, by omega, ?_, ?_⟩
    · simp
    · have := parity_prefix a (r % 2 ^ a) 0
      rw [oddCount_succ_right, this]; simp; omega
  · refine ⟨a + 1, r % 2 ^ a + 2 ^ a * 1, by omega, ?_, ?_⟩
    · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
    · have := parity_prefix a (r % 2 ^ a) 1
      rw [oddCount_succ_right, this]
      generalize 3 ^ oddCount a (r % 2 ^ a) = q at hodd ⊢
      omega

theorem coprime6_of_not_dvd (N : Nat) (h2 : N % 2 ≠ 0) (h3 : N % 3 ≠ 0) : Nat.Coprime N 6 := by
  unfold Nat.Coprime
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd N 6 := ⟨_, rfl⟩
  have h1 : g ∣ N := hg ▸ Nat.gcd_dvd_left N 6
  have h6 : g ∣ 6 := hg ▸ Nat.gcd_dvd_right N 6
  have hle : g ≤ 6 := Nat.le_of_dvd (by decide) h6
  rw [← hg]
  have hpos : 0 < g := Nat.pos_of_dvd_of_pos h6 (by decide)
  have hcases : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- `N = 2^a 3^b M` with `M` coprime to `6`. -/
theorem split_two_three (N : Nat) (hN : 1 ≤ N) :
    ∃ a b M, N = 2 ^ a * 3 ^ b * M ∧ Nat.Coprime M 6 := by
  induction N using Nat.strongRecOn with
  | _ N ih =>
    by_cases h2 : N % 2 = 0
    · obtain ⟨a, b, M, hM, hc⟩ := ih (N / 2) (by omega) (by omega)
      refine ⟨a + 1, b, M, ?_, hc⟩
      have : N = 2 * (N / 2) := by omega
      rw [this, hM, Nat.pow_succ]; grind
    · by_cases h3 : N % 3 = 0
      · obtain ⟨a, b, M, hM, hc⟩ := ih (N / 3) (by omega) (by omega)
        refine ⟨a, b + 1, M, ?_, hc⟩
        have : N = 3 * (N / 3) := by omega
        rw [this, hM, Nat.pow_succ 3 b]; grind
      · exact ⟨0, 0, N, by simp, coprime6_of_not_dvd N h2 h3⟩

theorem mod_combine_le {P Q n r : Nat} (hPQ : Nat.Coprime P Q) (hle : r ≤ n)
    (hP : n % P = r % P) (hQ : n % Q = r % Q) : n % (P * Q) = r % (P * Q) := by
  have h1 : P ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hP)
  have h2 : Q ∣ n - r := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hQ)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hPQ h1 h2
  have : n = r + (P * Q) * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_combine {P Q n r : Nat} (hPQ : Nat.Coprime P Q)
    (hP : n % P = r % P) (hQ : n % Q = r % Q) : n % (P * Q) = r % (P * Q) := by
  rcases Nat.le_total r n with h | h
  · exact mod_combine_le hPQ h hP hQ
  · exact (mod_combine_le hPQ h hP.symm hQ.symm).symm

/-- For odd `Q`, the class of `r' + 2^a s` modulo `Q` can be prescribed. -/
theorem exists_shift {Q : Nat} (hQ : Nat.Coprime Q 2) (a r' r : Nat) :
    ∃ s, (r' + 2 ^ a * s) % Q = r % Q := by
  have hQ1 : 1 ≤ Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · subst h; exact absurd hQ (by decide)
    · exact h
  haveI : NeZero Q := ⟨by omega⟩
  obtain ⟨b, hb⟩ := exists_inv_res (M := Q) (2 ^ a) (Nat.Coprime.pow_right a hQ)
  have hr' : r' ≤ r + Q * r' := by
    have : r' ≤ Q * r' := Nat.le_mul_of_pos_left r' hQ1
    omega
  refine ⟨b.val * (r + Q * r' - r'), ?_⟩
  apply (res_eq_iff Q _ _).1
  rw [res_add, res_mul, res_mul, res_val_self]
  have e1 : res Q (2 ^ a) * (b * res Q (r + Q * r' - r')) = res Q (r + Q * r' - r') := by
    calc res Q (2 ^ a) * (b * res Q (r + Q * r' - r'))
        = (res Q (2 ^ a) * b) * res Q (r + Q * r' - r') := by grind
      _ = res Q (r + Q * r' - r') := by rw [hb]; grind
  rw [e1, ← res_add]
  apply (res_eq_iff Q _ _).2
  have : r' + (r + Q * r' - r') = r + Q * r' := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_eq_of_le_sub {m X Y : Nat} (hle : Y ≤ X) (h : (X - Y) % m = 0) : X % m = Y % m := by
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
  have : X = Y + m * k := by omega
  rw [this, Nat.add_mul_mod_self_left]

theorem mod_add_left_cancel {m e X Y : Nat} (h : (e + X) % m = (e + Y) % m) : X % m = Y % m := by
  rcases Nat.le_total Y X with hle | hle
  · exact mod_eq_of_le_sub hle (by
      have := Nat.sub_mod_eq_zero_of_mod_eq h
      rwa [show e + X - (e + Y) = X - Y by omega] at this)
  · exact (mod_eq_of_le_sub hle (by
      have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
      rwa [show e + Y - (e + X) = Y - X by omega] at this)).symm

theorem cancel_three_pow {j Q e t s : Nat}
    (h : (e + 3 ^ j * t) % (3 ^ j * Q) = (e + 3 ^ j * s) % (3 ^ j * Q)) : t % Q = s % Q := by
  have h1 := mod_add_left_cancel h
  rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) h1

theorem cancel_three_pow_coprime {j M e t s : Nat} (hM : Nat.Coprime M 3)
    (h : (e + 3 ^ j * t) % M = (e + 3 ^ j * s) % M) : t % M = s % M := by
  have h1 := mod_add_left_cancel h
  rw [Nat.mul_comm, Nat.mul_comm (3 ^ j) s] at h1
  exact mod_cancel_mul_right (Nat.Coprime.pow_right j hM) h1

/-- A live class modulo `3^k` has a representative `d > B` modulo some deeper `3^(K+1)`. -/
theorem exists_lift (k B c : Nat) (hk : 1 ≤ k) (hc : c % 3 ≠ 0) :
    ∃ K d, k ≤ K ∧ d % 3 ≠ 0 ∧ d < 3 ^ (K + 1) ∧ d % 3 ^ k = c % 3 ^ k ∧ B < d := by
  refine ⟨k + B + 1, c % 3 ^ k + 3 ^ k * (B + 1), by omega, ?_, ?_, ?_, ?_⟩
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : c % 3 ^ (k' + 1) % 3 = c % 3 := Nat.mod_mod_of_dvd c (three_dvd_pow k')
    have h2 : 3 ^ (k' + 1) * (B + 1) = 3 * (3 ^ k' * (B + 1)) := by rw [Nat.pow_succ]; grind
    rw [h2]; omega
  · have hx : c % 3 ^ k < 3 ^ k := Nat.mod_lt _ (Nat.pow_pos (by decide))
    have h1 : B + 2 < 3 ^ (B + 2) := Nat.lt_pow_self (by decide)
    have hp : 0 < 3 ^ k := Nat.pow_pos (by decide)
    have h2 : 3 ^ k * (B + 2) < 3 ^ k * 3 ^ (B + 2) := (Nat.mul_lt_mul_left hp).2 h1
    have h3 : 3 ^ (k + B + 1 + 1) = 3 ^ k * 3 ^ (B + 2) := by
      rw [← Nat.pow_add]; congr 1
    have h4 : 3 ^ k * (B + 2) = 3 ^ k * (B + 1) + 3 ^ k := by grind
    omega
  · rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · have hp : 0 < 3 ^ k := Nat.pow_pos (by decide)
    have := Nat.le_mul_of_pos_left (B + 1) hp
    omega

/-- A node of the tree of `2w` in a prescribed live class modulo `3^k`, a prescribed class modulo `M`, and… -/
theorem density_input (M : Nat) [NeZero M] (h6 : Nat.Coprime M 6) {w : Nat} (hw3 : w % 3 ≠ 0)
    {k : Nat} (hk : 1 ≤ k) {c : Nat} (hc : c % 3 ≠ 0) (ρ B : Nat) :
    ∃ m, Tree (2 * w) m ∧ m % 3 ^ k = c % 3 ^ k ∧ m % M = ρ % M ∧ B < m := by
  obtain ⟨K, d, hkK, hd3, hdl, hdk, hdB⟩ := exists_lift k B c hk hc
  have hdvd : 3 ^ k ∣ 3 ^ (K + 1) := Nat.pow_dvd_pow 3 (by omega)
  obtain ⟨n, hn, hnc, _, hnr⟩ :=
    fiber_full M h6 (v := 2 * w) (by omega) (by omega) hd3 hdl (res M ρ)
  refine ⟨n, hn, ?_, (res_eq_iff M n ρ).1 hnr, ?_⟩
  · rw [← Nat.mod_mod_of_dvd _ hdvd, hnc, hdk]
  · have := Nat.mod_le n (3 ^ (K + 1)); omega

/-- The forward construction -/
theorem forward_construction (M : Nat) [NeZero M] (h6 : Nat.Coprime M 6) {w : Nat} (hw3 : w % 3 ≠ 0)
    (a' r' b s B : Nat) (hj : 1 ≤ oddCount a' r') :
    ∃ n, B < n ∧ Reaches w n ∧ n % 2 ^ a' = r' % 2 ^ a' ∧
      n % (3 ^ b * M) = (r' + 2 ^ a' * s) % (3 ^ b * M) := by
  have hM3 : Nat.Coprime M 3 := Nat.Coprime.coprime_dvd_right (by decide) h6
  have he3 : iter shortcut a' r' % 3 ≠ 0 := live_after_odd a' r' hj
  obtain ⟨j', hj'⟩ : ∃ j', oddCount a' r' = j' + 1 := ⟨oddCount a' r' - 1, by omega⟩
  have hlive : (iter shortcut a' r' + 3 ^ oddCount a' r' * s) % 3 ≠ 0 := by
    have h1 : 3 ^ oddCount a' r' * s = 3 * (3 ^ j' * s) := by rw [hj', Nat.pow_succ]; grind
    rw [h1]; omega
  obtain ⟨m, hm, hm3, hmM, hmB⟩ :=
    density_input M h6 hw3 (k := oddCount a' r' + b) (by omega) hlive
      (iter shortcut a' r' + 3 ^ oddCount a' r' * s)
      (iter shortcut a' r' + 3 ^ oddCount a' r' * B)
  have hmod : m % 3 ^ oddCount a' r' = iter shortcut a' r' % 3 ^ oddCount a' r' := by
    have hd : 3 ^ oddCount a' r' ∣ 3 ^ (oddCount a' r' + b) := Nat.pow_dvd_pow 3 (by omega)
    rw [← Nat.mod_mod_of_dvd m hd, hm3, Nat.mod_mod_of_dvd _ hd, Nat.add_mul_mod_self_left]
  have hge : iter shortcut a' r' ≤ m := by omega
  have hdiv : 3 ^ oddCount a' r' ∣ m - iter shortcut a' r' :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
  obtain ⟨t, ht⟩ := hdiv
  have hmt : m = iter shortcut a' r' + 3 ^ oddCount a' r' * t := by omega
  have htB : B < t := by
    have : 3 ^ oddCount a' r' * B < 3 ^ oddCount a' r' * t := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have ht3 : t % 3 ^ b = s % 3 ^ b := by
    rw [hmt, Nat.pow_add] at hm3
    exact cancel_three_pow hm3
  have htM : t % M = s % M := by
    rw [hmt] at hmM
    exact cancel_three_pow_coprime hM3 hmM
  have htQ : t % (3 ^ b * M) = s % (3 ^ b * M) :=
    mod_combine (Nat.Coprime.pow_left b hM3.symm) ht3 htM
  refine ⟨r' + 2 ^ a' * t, ?_, ?_, ?_, ?_⟩
  · have hp2 : 0 < 2 ^ a' := Nat.pow_pos (by decide)
    have := Nat.le_mul_of_pos_left t hp2
    omega
  · have hT : iter shortcut a' (r' + 2 ^ a' * t) = iter shortcut a' r' + 3 ^ oddCount a' r' * t :=
      parity_prefix a' r' t
    have h1 : Reaches (iter shortcut a' r' + 3 ^ oddCount a' r' * t) (r' + 2 ^ a' * t) := by
      rw [← hT]; exact reaches_iter_shortcut a' _
    have hsw : Reaches w (2 * w) := ⟨1, by simp [iter, collatz_double]⟩
    rw [← hmt] at h1
    exact reaches_trans h1 (reaches_trans (tree_reaches hm) hsw)
  · rw [Nat.add_mul_mod_self_left]
  · rw [Nat.add_mod, Nat.mul_mod, htQ, ← Nat.mul_mod, ← Nat.add_mod]

/-- **Every Remainder Everywhere.** For every `N ≥ 1`, every `w` with `3 ∤ w`, every `r` and -/
theorem every_remainder_everywhere (N : Nat) (hN : 1 ≤ N) (w : Nat) (hw3 : w % 3 ≠ 0) (r B : Nat) :
    ∃ n : Nat, B < n ∧ Reaches w n ∧ n % N = r % N := by
  obtain ⟨a, b, M, rfl, h6⟩ := split_two_three N hN
  haveI : NeZero M := ⟨fun h => by subst h; exact absurd h6 (by decide)⟩
  obtain ⟨a', r', haa, hr', hj⟩ := exists_odd_prefix a r
  have hQ2 : Nat.Coprime (3 ^ b * M) 2 :=
    Nat.Coprime.mul_left (Nat.Coprime.pow_left b (by decide))
      (Nat.Coprime.coprime_dvd_right (by decide) h6)
  obtain ⟨s, hs⟩ := exists_shift hQ2 a' r' r
  obtain ⟨n, hnB, hnw, hn2, hnQ⟩ := forward_construction M h6 hw3 a' r' b s B hj
  refine ⟨n, hnB, hnw, ?_⟩
  have h2 : n % 2 ^ a = r % 2 ^ a := by
    rw [← Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 haa), hn2,
      Nat.mod_mod_of_dvd r' (Nat.pow_dvd_pow 2 haa), hr']
  have hQ : n % (3 ^ b * M) = r % (3 ^ b * M) := hnQ.trans hs
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b * M) := Nat.Coprime.pow_left a hQ2.symm
  have := mod_combine hcop h2 hQ
  rwa [← Nat.mul_assoc] at this

#print axioms every_remainder_everywhere

end ERE
