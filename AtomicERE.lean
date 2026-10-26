import Mathlib

/-!
# Atomic ERE
Only the atomic inverse Collatz steps:  D n = 2n,  U n = (n-1)/3 (when n % 6 = 4).
Nodes carry (n % 3^(K+1), n % 2).  Flag 0 = even, flag 1 = odd (reached by U).

No `sorry` left (`principal_order` is proved but no longer used by the main chain).
`flat_four_pow` and `flat_contra` are proved by the elementary route (flat_hom + four_pow_modEq_one_iff).

-/

namespace AtomicERE

variable (p : ℕ) [Fact p.Prime]

instance instNeZeroAtomic : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-! ## Collatz layer -/

def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

def Reaches (v n : ℕ) : Prop := ∃ k, collatz^[k] n = v

theorem collatz_double (a : ℕ) : collatz (2 * a) = a := by
  unfold collatz
  split_ifs with h <;> omega

theorem collatz_pow_mul (j m : ℕ) : collatz^[j] (2 ^ j * m) = m := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 ^ (j + 1) * m = 2 * (2 ^ j * m) by ring,
      Function.iterate_succ_apply, collatz_double, ih]

theorem reaches_trans {a b c : ℕ} (h1 : Reaches b a) (h2 : Reaches c b) : Reaches c a := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [Function.iterate_add_apply, hk1, hk2]⟩

theorem collatz_eq_iff (m n : ℕ) :
    collatz m = n ↔ m = 2 * n ∨ (m % 2 = 1 ∧ 3 * m + 1 = n) := by
  unfold collatz
  split_ifs with h <;> omega

theorem pred_of_three_dvd {m n : ℕ} (hn : n % 3 = 0) (h : collatz m = n) : m = 2 * n := by
  rcases (collatz_eq_iff m n).1 h with h1 | ⟨h2, h3⟩ <;> omega

/-! ### Complement (3 ∣ w) -/

theorem reaches_of_three_dvd {w : ℕ} (hw : w % 3 = 0) {n : ℕ} :
    Reaches w n ↔ ∃ k, n = 2 ^ k * w := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing n with
    | zero => exact ⟨0, by simpa using hk⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply] at hk
      obtain ⟨j, hj⟩ := ih hk
      by_cases hev : n % 2 = 0
      · refine ⟨j + 1, ?_⟩
        have hc : collatz n = n / 2 := by unfold collatz; simp [hev]
        rw [hc] at hj
        have hp : 2 ^ (j + 1) * w = 2 * (2 ^ j * w) := by ring
        rw [hp]; omega
      · exfalso
        have hc : collatz n = 3 * n + 1 := by unfold collatz; simp [hev]
        rw [hc] at hj
        obtain ⟨a, ha⟩ : 3 ∣ w := Nat.dvd_of_mod_eq_zero hw
        have h3 : 2 ^ j * w = 3 * (2 ^ j * a) := by rw [ha]; ring
        omega
  · rintro ⟨k, rfl⟩
    exact ⟨k, collatz_pow_mul k w⟩

theorem attained_residues_of_three_dvd {w : ℕ} (hw : w % 3 = 0) (r : ZMod p) :
    (∃ n, Reaches w n ∧ (n : ZMod p) = r) ↔ ∃ k : ℕ, (2 : ZMod p) ^ k * (w : ZMod p) = r := by
  constructor
  · rintro ⟨n, hn, hr⟩
    obtain ⟨k, rfl⟩ := (reaches_of_three_dvd hw).1 hn
    exact ⟨k, by rw [← hr]; push_cast; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨2 ^ k * w, ⟨k, collatz_pow_mul k w⟩, by rw [← hk]; push_cast; ring⟩

/-! ## The atomic tree -/

inductive Tree (v : ℕ) : ℕ → Prop
  | seed : Tree v v
  | D {n : ℕ} : Tree v n → Tree v (2 * n)
  | U {n : ℕ} : Tree v n → n % 6 = 4 → ((n - 1) / 3) % 3 ≠ 0 → Tree v ((n - 1) / 3)

theorem Tree_live {v n : ℕ} (hv3 : v % 3 ≠ 0) (h : Tree v n) : n % 3 ≠ 0 := by
  induction h with
  | seed => exact hv3
  | D _ ih => omega
  | U _ _ h3 _ => exact h3

theorem Tree_reaches {v n : ℕ} (h : Tree v n) : Reaches v n := by
  induction h with
  | seed => exact ⟨0, rfl⟩
  | @D n _ ih =>
    exact reaches_trans (⟨1, by simp [collatz_double]⟩ : Reaches n (2 * n)) ih
  | @U n _ h6 _ ih =>
    have h1 : collatz ((n - 1) / 3) = n := by
      unfold collatz; split_ifs with h <;> omega
    exact reaches_trans (⟨1, by simpa using h1⟩ : Reaches n ((n - 1) / 3)) ih

theorem tree_odd_inv {v n : ℕ} (hv : v % 2 = 0) (h : Tree v n) (hodd : n % 2 = 1) :
    ∃ m, Tree v m ∧ m % 6 = 4 ∧ ((m - 1) / 3) % 3 ≠ 0 ∧ n = (m - 1) / 3 := by
  cases h with
  | seed => omega
  | D _ => omega
  | U hm h6 h3 => exact ⟨_, hm, h6, h3, rfl⟩

/-! ## Arithmetic helpers -/

theorem two_ne_zero_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h'
  have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem three_ne_zero_zmod (hp5 : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h'
  have : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem three_dvd_pow (K : ℕ) : 3 ∣ 3 ^ (K + 1) := dvd_pow_self 3 (Nat.succ_ne_zero K)

theorem one_lt_pow3 (K : ℕ) : 1 < 3 ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by norm_num)

theorem mod_unit {M c : ℕ} (h3 : 3 ∣ M) (hc : c % 3 ≠ 0) : c % M % 3 ≠ 0 := by
  rw [Nat.mod_mod_of_dvd c h3]; exact hc

lemma four_pow_mod_three (j : ℕ) : 4 ^ j % 3 = 1 := by
  induction j with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma two_pow_mod_three_ne (E : ℕ) : 2 ^ E % 3 ≠ 0 := by
  induction E with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem lte_four {n : ℕ} (hn : n ≠ 0) :
    padicValNat 3 (4 ^ n - 1) = 1 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    ⟨1, by norm_num⟩ (by norm_num) (by norm_num) (by norm_num) hn
  have e1 : (1 : ℕ) ^ n = 1 := one_pow n
  rw [e1] at h
  have h1 : padicValNat 3 (4 - 1) = 1 := by
    exact padicValNat_self
  rw [h1] at h
  exact h

theorem four_pow_modEq_one_iff {K m : ℕ} :
    4 ^ m ≡ 1 [MOD 3 ^ (K + 1)] ↔ 3 ^ K ∣ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun _ => dvd_zero _, fun _ => by simp [Nat.ModEq]⟩
  · have hm0 : m ≠ 0 := by omega
    have hpos : 0 < 4 ^ m := by positivity
    have hgt : 1 < 4 ^ m := Nat.one_lt_pow hm0 (by norm_num)
    have hne : 4 ^ m - 1 ≠ 0 := by omega
    rw [show (4 ^ m ≡ 1 [MOD 3 ^ (K + 1)]) ↔ (1 ≡ 4 ^ m [MOD 3 ^ (K + 1)]) from
        ⟨fun h => h.symm, fun h => h.symm⟩, Nat.modEq_iff_dvd' hpos,
      padicValNat_dvd_iff_le (p := 3) hne, lte_four hm0,
      padicValNat_dvd_iff_le (p := 3) hm0]
    omega

/-- The order of 2 modulo 3^(K+1) is 2·3^K. -/
lemma two_pow_modEq_one_iff {K m : ℕ} :
    2 ^ m ≡ 1 [MOD 3 ^ (K + 1)] ↔ 2 * 3 ^ K ∣ m := by
  constructor
  · intro h
    have h3 : 2 ^ m ≡ 1 [MOD 3] := Nat.ModEq.of_dvd (three_dvd_pow K) h
    have hev : m % 2 = 0 := by
      by_contra hodd
      obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
      have e : 2 ^ (2 * n + 1) = 2 * 4 ^ n := by
        rw [pow_succ, pow_mul]; norm_num; try ring
      have h4 := four_pow_mod_three n
      unfold Nat.ModEq at h3
      rw [e] at h3
      omega
    obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    have e : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [e] at h
    exact mul_dvd_mul_left 2 ((four_pow_modEq_one_iff (K := K) (m := n)).1 h)
  · rintro ⟨q, rfl⟩
    have h : 4 ^ (3 ^ K) ≡ 1 [MOD 3 ^ (K + 1)] := (four_pow_modEq_one_iff).2 dvd_rfl
    have e : 2 ^ (2 * 3 ^ K * q) = (4 ^ (3 ^ K)) ^ q := by
      rw [pow_mul, pow_mul]; norm_num
    rw [e]
    have := h.pow q
    rwa [one_pow] at this

lemma two_pow_inj {K E1 E2 : ℕ} (h1 : E1 < 2 * 3 ^ K) (h2 : E2 < 2 * 3 ^ K)
    (h : 2 ^ E1 ≡ 2 ^ E2 [MOD 3 ^ (K + 1)]) : E1 = E2 := by
  have key : ∀ a b : ℕ, a ≤ b → b < 2 * 3 ^ K →
      2 ^ a ≡ 2 ^ b [MOD 3 ^ (K + 1)] → a = b := by
    intro a b hab hb h
    have hcop : Nat.gcd (3 ^ (K + 1)) (2 ^ a) = 1 :=
      Nat.Coprime.pow (K + 1) a (by norm_num)
    have hb' : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by
      rw [← pow_add]; congr 1; omega
    rw [hb'] at h
    have h' : 2 ^ a * 1 ≡ 2 ^ a * 2 ^ (b - a) [MOD 3 ^ (K + 1)] := by rwa [mul_one]
    have h'' := (Nat.ModEq.cancel_left_of_coprime hcop h').symm
    have hd := (two_pow_modEq_one_iff (K := K)).1 h''
    have : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  rcases le_total E1 E2 with hle | hle
  · exact key _ _ hle h2 h
  · exact (key _ _ hle h1 h.symm).symm

/-- Multiplication by 2 is a single cycle on the units modulo 3^(K+1). -/
theorem two_transitive {K c d : ℕ} (_hK : 1 ≤ K) (hc : c % 3 ≠ 0) (hd : d % 3 ≠ 0)
    (hdl : d < 3 ^ (K + 1)) :
    ∃ j, (2 ^ j * c) % 3 ^ (K + 1) = d := by
  classical
  have hcop : Nat.gcd (3 ^ (K + 1)) c = 1 :=
    Nat.Coprime.pow_left (K + 1)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  have hM : 3 ^ (K + 1) = 3 * 3 ^ K := by ring
  have hpos : 0 < 3 ^ K := by positivity
  have hmap : ∀ E ∈ Finset.range (2 * 3 ^ K), (2 ^ E * c) % 3 ^ (K + 1) ∈
      (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 ≠ 0) := by
    intro E _
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [Nat.mod_mod_of_dvd _ (three_dvd_pow K)]
    have hnd : ¬ 3 ∣ 2 ^ E * c := by
      intro hdv
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 hdv with h | h
      · exact two_pow_mod_three_ne E (Nat.mod_eq_zero_of_dvd h)
      · exact hc (Nat.mod_eq_zero_of_dvd h)
    exact fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  have hinj : ∀ E1 E2, E1 ∈ Finset.range (2 * 3 ^ K) → E2 ∈ Finset.range (2 * 3 ^ K) →
      (2 ^ E1 * c) % 3 ^ (K + 1) = (2 ^ E2 * c) % 3 ^ (K + 1) → E1 = E2 := by
    intro E1 E2 h1 h2 h
    rw [Finset.mem_range] at h1 h2
    have h' : 2 ^ E1 * c ≡ 2 ^ E2 * c [MOD 3 ^ (K + 1)] := h
    exact two_pow_inj h1 h2 (Nat.ModEq.cancel_right_of_coprime hcop h')
  have hcard : ((Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 ≠ 0)).card
      ≤ (Finset.range (2 * 3 ^ K)).card := by
    have hsub : (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 ≠ 0)
        ⊆ (Finset.range (2 * 3 ^ K)).image (fun j => 3 * (j / 2) + 1 + j % 2) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_range] at hw
      rw [Finset.mem_image]
      exact ⟨2 * (w / 3) + (w % 3 - 1), Finset.mem_range.2 (by omega), by omega⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hdm : d ∈ (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hdl, hd⟩
  obtain ⟨E, _, hwE⟩ := Finset.surj_on_of_inj_on_of_card_le
    (fun E _ => (2 ^ E * c) % 3 ^ (K + 1)) hmap hinj hcard d hdm
  exact ⟨E, hwE.symm⟩

/-- 4^(3^n) = 1 + 3^(n+1) + 3^(n+2)·q. -/
lemma four_pow_form (n : ℕ) : ∃ q : ℕ, 4 ^ (3 ^ n) = 1 + 3 ^ (n + 1) + 3 ^ (n + 2) * q := by
  induction n with
  | zero => exact ⟨0, by norm_num⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q + 3 ^ n * (1 + 3 * q) ^ 2 + (3 ^ n) ^ 2 * (1 + 3 * q) ^ 3, ?_⟩
    rw [pow_succ 3 n, pow_mul, hq]
    ring

theorem four_pow_cong {K : ℕ} (hK : 1 ≤ K) :
    4 ^ (3 ^ (K - 1)) % 3 ^ (K + 1) = (1 + 3 ^ K) % 3 ^ (K + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨q, hq⟩ := four_pow_form n
  rw [hq]
  exact Nat.add_mul_mod_self_left _ _ _

/-! ## Fibres -/

def fibre (K v c f : ℕ) : Set (ZMod p) :=
  {t | ∃ n, Tree v n ∧ n % 3 ^ (K + 1) = c ∧ n % 2 = f ∧ (n : ZMod p) = t}

theorem fibre_proj {J K v c f : ℕ} (hJK : J ≤ K) {t : ZMod p} (ht : t ∈ fibre p K v c f) :
    t ∈ fibre p J v (c % 3 ^ (J + 1)) f := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨n, hn, ?_, hf, hnt⟩
  rw [← hc, Nat.mod_mod_of_dvd _ (pow_dvd_pow 3 (by omega))]

theorem fibre_D_image {K v c f : ℕ} {t : ZMod p} (ht : t ∈ fibre p K v c f) :
    2 * t ∈ fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨2 * n, Tree.D hn, ?_, by omega, by rw [← hnt]; push_cast; ring⟩
  subst hc
  exact (Nat.mul_mod_mod 2 n _).symm

theorem fibre_D_ncard_le (hp5 : 5 ≤ p) (K v c f : ℕ) :
    (fibre p K v c f).ncard ≤ (fibre p K v ((2 * c) % 3 ^ (K + 1)) 0).ncard := by
  have hinj : Function.Injective (fun t : ZMod p => 2 * t) :=
    mul_right_injective₀ (two_ne_zero_zmod p hp5)
  have hsub : (fun t : ZMod p => 2 * t) '' (fibre p K v c f)
      ⊆ fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact fibre_D_image p ht
  calc (fibre p K v c f).ncard
      = ((fun t : ZMod p => 2 * t) '' (fibre p K v c f)).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

/-- Iterating D on even fibres. -/
theorem fibre_card_iter (hp5 : 5 ≤ p) (K v : ℕ) :
    ∀ (j c : ℕ), c < 3 ^ (K + 1) → c % 3 ≠ 0 →
      (fibre p K v c 0).ncard ≤ (fibre p K v ((2 ^ j * c) % 3 ^ (K + 1)) 0).ncard := by
  intro j
  induction j with
  | zero =>
    intro c hc _
    have h0 : (2 ^ 0 * c) % 3 ^ (K + 1) = c := by
      rw [pow_zero, one_mul]; exact Nat.mod_eq_of_lt hc
    exact le_of_eq (by rw [h0])
  | succ j ih =>
    intro c hc hc3
    have h1 := fibre_D_ncard_le p hp5 K v c 0
    have hd3 : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 := mod_unit (three_dvd_pow K) (by omega)
    have h2 := ih ((2 * c) % 3 ^ (K + 1)) (Nat.mod_lt _ (by positivity)) hd3
    have e : (2 ^ j * ((2 * c) % 3 ^ (K + 1))) % 3 ^ (K + 1)
        = (2 ^ (j + 1) * c) % 3 ^ (K + 1) := by
      rw [Nat.mul_mod_mod, pow_succ]; congr 1; ring
    rw [e] at h2
    exact h1.trans h2

theorem fibre_card_const (hp5 : 5 ≤ p) {K v c d : ℕ} (hK : 1 ≤ K)
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) (hd : d % 3 ≠ 0) (hdl : d < 3 ^ (K + 1)) :
    (fibre p K v c 0).ncard = (fibre p K v d 0).ncard := by
  obtain ⟨j, hj⟩ := two_transitive hK hc hd hdl
  obtain ⟨i, hi⟩ := two_transitive hK hd hc hcl
  have h1 := fibre_card_iter p hp5 K v j c hcl hc
  have h2 := fibre_card_iter p hp5 K v i d hdl hd
  rw [hj] at h1
  rw [hi] at h2
  exact le_antisymm h1 h2

theorem fibre_D_eq (hp5 : 5 ≤ p) {K v c : ℕ} (hK : 1 ≤ K)
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 = (fun t : ZMod p => 2 * t) '' (fibre p K v c 0) := by
  have hinj : Function.Injective (fun t : ZMod p => 2 * t) :=
    mul_right_injective₀ (two_ne_zero_zmod p hp5)
  have hsub : (fun t : ZMod p => 2 * t) '' (fibre p K v c 0)
      ⊆ fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact fibre_D_image p ht
  have hcard : (fibre p K v ((2 * c) % 3 ^ (K + 1)) 0).ncard
      ≤ ((fun t : ZMod p => 2 * t) '' (fibre p K v c 0)).ncard := by
    rw [Set.ncard_image_of_injective _ hinj]
    have hd : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 :=
      mod_unit (three_dvd_pow K) (by omega)
    exact (fibre_card_const p hp5 hK hd (Nat.mod_lt _ (by positivity)) hc hcl).le
  exact (Set.eq_of_subset_of_ncard_le hsub hcard).symm

theorem fibre_flag1_sub (hp5 : 5 ≤ p) {K v c : ℕ} (hK : 1 ≤ K)
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    fibre p K v c 1 ⊆ fibre p K v c 0 := by
  intro t ht
  have h1 := fibre_D_image p ht
  rw [fibre_D_eq p hp5 hK hc hcl] at h1
  obtain ⟨t', ht', e⟩ := h1
  have : t' = t := mul_left_cancel₀ (two_ne_zero_zmod p hp5) e
  rwa [this] at ht'

/-- The U-source of an odd fibre. -/
theorem fibre_U_iff (hp5 : 5 ≤ p) {K v t0 : ℕ} (hv : v % 2 = 0) (_hv3 : v % 3 ≠ 0)
    (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) (t : ZMod p) :
    t ∈ fibre p K v t0 1 ↔
      3 * t + 1 ∈ fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0 := by
  have hpow : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by ring
  constructor
  · rintro ⟨n, hn, hc, hf, hnt⟩
    obtain ⟨m, hm, h6, h3, hnm⟩ := tree_odd_inv hv hn hf
    have hm3 : m = 3 * n + 1 := by omega
    refine ⟨m, hm, ?_, by omega, ?_⟩
    · have hmod : n ≡ t0 [MOD 3 ^ (K + 1)] := by
        unfold Nat.ModEq; rw [hc, Nat.mod_eq_of_lt ht0l]
      have h1 := (Nat.ModEq.mul_left' 3 hmod).add_right 1
      rw [← pow_succ'] at h1
      rw [hm3]; exact h1
    · rw [hm3, ← hnt]
      (push_cast; ring)
  · rintro ⟨m, hm, hc, hf, hmt⟩
    have hdiv3 : 3 ∣ 3 ^ (K + 1 + 1) := three_dvd_pow (K + 1)
    have hdiv9 : 9 ∣ 3 ^ (K + 1 + 1) := by
      have : 3 ^ 2 ∣ 3 ^ (K + 1 + 1) := pow_dvd_pow 3 (by omega)
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
      rw [← hqd, hc, Nat.mod_eq_of_lt (by omega : 3 * t0 + 1 < 3 ^ (K + 1 + 1))] at hq
      have hq' : 3 ^ (K + 1 + 1) * q = 3 * (3 ^ (K + 1) * q) := by rw [hpow]; ring
      have e : n = t0 + 3 ^ (K + 1) * q := by omega
      rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht0l]
    · have hcm : (m : ZMod p) = 3 * (n : ZMod p) + 1 := by
        rw [hm']; (push_cast; ring)
      have h3 := three_ne_zero_zmod p hp5
      exact mul_left_cancel₀ h3 (by linear_combination hmt - hcm)

/-! ### Stabilisation -/

noncomputable def sig (K v : ℕ) : ℕ := (fibre p K v 1 0).ncard

theorem sig_antitone (K v : ℕ) (_hK : 1 ≤ K) : sig p (K + 1) v ≤ sig p K v := by
  have hsub : fibre p (K + 1) v 1 0 ⊆ fibre p K v 1 0 := by
    intro t ht
    have h := fibre_proj p (Nat.le_succ K) ht
    rwa [Nat.mod_eq_of_lt (one_lt_pow3 K)] at h
  exact Set.ncard_le_ncard hsub

theorem sig_pos (hp5 : 5 ≤ p) {v : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (K : ℕ) (hK : 1 ≤ K) : 1 ≤ sig p K v := by
  have hne : (fibre p K v (v % 3 ^ (K + 1)) 0).Nonempty :=
    ⟨(v : ZMod p), v, Tree.seed, rfl, hv, rfl⟩
  have hpos : 0 < (fibre p K v (v % 3 ^ (K + 1)) 0).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 hne
  have heq := fibre_card_const p hp5 (v := v) hK (mod_unit (three_dvd_pow K) hv3)
    (Nat.mod_lt _ (by positivity)) (by norm_num : 1 % 3 ≠ 0) (one_lt_pow3 K)
  unfold sig; omega

theorem fibre1_card (hp5 : 5 ≤ p) {K v t0 : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (hK : 1 ≤ K) (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) :
    (fibre p K v t0 1).ncard = sig p (K + 1) v := by
  have hset : fibre p K v t0 1 = (fun t : ZMod p => 3 * t + 1) ⁻¹'
      (fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0) := by
    ext t; exact fibre_U_iff p hp5 hv hv3 ht0 ht0l t
  have h3 := three_ne_zero_zmod p hp5
  have hinj : Function.Injective (fun t : ZMod p => 3 * t + 1) :=
    fun a b h => mul_left_cancel₀ h3 (add_right_cancel h)
  have hrange : fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0
      ⊆ Set.range (fun t : ZMod p => 3 * t + 1) := by
    intro a _
    refine ⟨(a - 1) / 3, ?_⟩
    show 3 * ((a - 1) / 3) + 1 = a
    field_simp
    try ring
  rw [hset, Set.ncard_preimage_of_injective_subset_range hinj hrange]
  have he : (3 * t0 + 1) % 3 ^ (K + 1 + 1) % 3 ≠ 0 :=
    mod_unit (three_dvd_pow (K + 1)) (by omega)
  exact fibre_card_const p hp5 (K := K + 1) (by omega) he (Nat.mod_lt _ (by positivity))
    (by norm_num : 1 % 3 ≠ 0) (one_lt_pow3 (K + 1))

def Stab (v K0 : ℕ) : Prop :=
  ∀ K, K0 ≤ K → 1 ≤ K →
    (∀ c, c % 3 ≠ 0 → c < 3 ^ (K + 1) → fibre p K v c 1 = fibre p K v c 0) ∧
    (∀ e, e % 3 ≠ 0 → e < 3 ^ (K + 2) → fibre p (K + 1) v e 0 = fibre p K v (e % 3 ^ (K + 1)) 0)

/-- Stabilisation of fibre cardinalities, via `Nat.find`. -/
theorem stabilization (hp5 : 5 ≤ p) {v : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0) :
    ∃ K0, 1 ≤ K0 ∧ Stab p v K0 := by
  classical
  have hex : ∃ m, ∃ K, 1 ≤ K ∧ sig p K v = m := ⟨_, 1, le_refl _, rfl⟩
  obtain ⟨K0, hK0, hm⟩ := Nat.find_spec hex
  have hmin : ∀ K, 1 ≤ K → Nat.find hex ≤ sig p K v :=
    fun K hK => Nat.find_min' hex ⟨K, hK, rfl⟩
  have hdown : ∀ K, K0 ≤ K → sig p K v ≤ sig p K0 v := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => exact le_refl _
    | succ K hK ih => exact (sig_antitone p K v (by omega)).trans ih
  have hconst : ∀ K, K0 ≤ K → sig p K v = Nat.find hex := by
    intro K hK
    have h1 := hdown K hK
    have h2 := hmin K (by omega)
    omega
  refine ⟨K0, hK0, ?_⟩
  intro K hK hK1
  have hσK := hconst K hK
  have hσK1 := hconst (K + 1) (by omega)
  constructor
  · intro c hc hcl
    have hsub := fibre_flag1_sub p hp5 (v := v) hK1 hc hcl
    have c1 : (fibre p K v c 1).ncard = sig p (K + 1) v := fibre1_card p hp5 hv hv3 hK1 hc hcl
    have c0 : (fibre p K v c 0).ncard = sig p K v :=
      fibre_card_const p hp5 hK1 hc hcl (by norm_num : 1 % 3 ≠ 0) (one_lt_pow3 K)
    exact Set.eq_of_subset_of_ncard_le hsub (by omega)
  · intro e he hel
    have hsub : fibre p (K + 1) v e 0 ⊆ fibre p K v (e % 3 ^ (K + 1)) 0 :=
      fun t ht => fibre_proj p (Nat.le_succ K) ht
    have c1 : (fibre p (K + 1) v e 0).ncard = sig p (K + 1) v :=
      fibre_card_const p hp5 (by omega) he hel (by norm_num : 1 % 3 ≠ 0) (one_lt_pow3 (K + 1))
    have c0 : (fibre p K v (e % 3 ^ (K + 1)) 0).ncard = sig p K v :=
      fibre_card_const p hp5 hK1 (mod_unit (three_dvd_pow K) he) (Nat.mod_lt _ (by positivity))
        (by norm_num : 1 % 3 ≠ 0) (one_lt_pow3 K)
    exact Set.eq_of_subset_of_ncard_le hsub (by omega)

/-! ## Affine labels and walks -/

abbrev Aff := ZMod p × ZMod p

def aapp (f : Aff p) (t : ZMod p) : ZMod p := f.1 * t + f.2
def athen (f g : Aff p) : Aff p := (g.1 * f.1, g.1 * f.2 + g.2)
def ainv (f : Aff p) : Aff p := (f.1⁻¹, -(f.1⁻¹ * f.2))

theorem athen_app (f g : Aff p) (t : ZMod p) :
    aapp p (athen p f g) t = aapp p g (aapp p f t) := by
  simp [athen, aapp]; ring

theorem athen_assoc (f g h : Aff p) :
    athen p (athen p f g) h = athen p f (athen p g h) :=
  Prod.ext (by simp only [athen]; ring) (by simp only [athen]; ring)

theorem athen_one_left (g : Aff p) :
    athen p ((1 : ZMod p), (0 : ZMod p)) g = g :=
  Prod.ext (by simp [athen]) (by simp [athen])

theorem athen_one_right (f : Aff p) :
    athen p f ((1 : ZMod p), (0 : ZMod p)) = f :=
  Prod.ext (by simp [athen]) (by simp [athen])

theorem ainv_app (f : Aff p) (hf : f.1 ≠ 0) (t : ZMod p) :
    aapp p (ainv p f) (aapp p f t) = t := by
  simp [ainv, aapp]; field_simp; ring

theorem ainv_ainv (f : Aff p) (hf : f.1 ≠ 0) : ainv p (ainv p f) = f := by
  apply Prod.ext
  · simp [ainv]
  · simp [ainv, hf]

theorem ainv_athen (f g : Aff p) (hf : f.1 ≠ 0) (hg : g.1 ≠ 0) :
    ainv p (athen p f g) = athen p (ainv p g) (ainv p f) := by
  apply Prod.ext
  · simp only [athen, ainv, mul_inv]; ring
  · simp only [athen, ainv, mul_inv]
    field_simp
    ring

theorem aapp_inj (f : Aff p) (hf : f.1 ≠ 0) : Function.Injective (aapp p f) := by
  intro a b hab
  have hab' : f.1 * a + f.2 = f.1 * b + f.2 := hab
  exact mul_left_cancel₀ hf (add_right_cancel hab')

inductive Edge (K : ℕ) : ℕ × ℕ → ℕ × ℕ → Aff p → Prop
  | D {c f : ℕ} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
      Edge K (c, f) ((2 * c) % 3 ^ (K + 1), 0) ((2 : ZMod p), 0)
  | U {e : ℕ} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
      Edge K (e % 3 ^ (K + 1), 0) (((e - 1) / 3) % 3 ^ (K + 1), 1)
        (((3 : ZMod p))⁻¹, -((3 : ZMod p))⁻¹)

inductive Walk (K : ℕ) : ℕ × ℕ → ℕ × ℕ → Aff p → Prop
  | nil (c : ℕ × ℕ) : Walk K c c (1, 0)
  | fwd {u w d : ℕ × ℕ} {f g : Aff p} :
      Edge p K u w f → Walk K w d g → Walk K u d (athen p f g)
  | bwd {u w d : ℕ × ℕ} {f g : Aff p} :
      Edge p K u w f → Walk K u d g → Walk K w d (athen p (ainv p f) g)

def base : ℕ × ℕ := (1, 0)

def Hol (K : ℕ) : Set (Aff p) := {f | Walk p K base base f}

def HasTranslation (K : ℕ) : Prop :=
  ∃ d : ZMod p, d ≠ 0 ∧ ((1 : ZMod p), d) ∈ Hol p K

theorem Walk.append {K : ℕ} {u w d : ℕ × ℕ} {f g : Aff p}
    (h1 : Walk p K u w f) (h2 : Walk p K w d g) :
    Walk p K u d (athen p f g) := by
  revert g
  induction h1 with
  | nil c =>
    intro g h2
    rw [athen_one_left]
    exact h2
  | fwd he hw ih =>
    intro g h2
    have h3 := Walk.fwd he (ih h2)
    rw [athen_assoc]
    exact h3
  | bwd he hw ih =>
    intro g h2
    have h3 := Walk.bwd he (ih h2)
    rw [athen_assoc]
    exact h3

theorem Edge.label_unit (hp5 : 5 ≤ p) {K : ℕ} {u w : ℕ × ℕ} {f : Aff p}
    (h : Edge p K u w f) : f.1 ≠ 0 := by
  cases h with
  | D hc hlt hf => exact two_ne_zero_zmod p hp5
  | U h1 h9 hlt => exact inv_ne_zero (three_ne_zero_zmod p hp5)

theorem Edge.src_valid {K : ℕ} {u w : ℕ × ℕ} {f : Aff p} (h : Edge p K u w f) :
    u.1 % 3 ≠ 0 ∧ u.1 < 3 ^ (K + 1) ∧ u.2 < 2 := by
  cases h with
  | D hc hlt hf => exact ⟨hc, hlt, hf⟩
  | U h1 h9 hlt =>
    exact ⟨mod_unit (three_dvd_pow K) (by omega), Nat.mod_lt _ (by positivity), by norm_num⟩

theorem Walk.label_unit (hp5 : 5 ≤ p) {K : ℕ} {u w : ℕ × ℕ} {f : Aff p}
    (h : Walk p K u w f) : f.1 ≠ 0 := by
  induction h with
  | nil c => simp
  | fwd he hw ih =>
    simp only [athen]
    exact mul_ne_zero ih (Edge.label_unit p hp5 he)
  | bwd he hw ih =>
    simp only [athen, ainv]
    exact mul_ne_zero ih (inv_ne_zero (Edge.label_unit p hp5 he))

theorem Walk.symm (hp5 : 5 ≤ p) {K : ℕ} {u w : ℕ × ℕ} {f : Aff p}
    (h : Walk p K u w f) : Walk p K w u (ainv p f) := by
  induction h with
  | nil c =>
    have e : ainv p ((1 : ZMod p), (0 : ZMod p)) = (1, 0) := by simp [ainv]
    rw [e]; exact Walk.nil c
  | @fwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have hg := Walk.label_unit p hp5 hw
    have key := Walk.append p ih (Walk.bwd he (Walk.nil u))
    have e : ainv p (athen p f g)
        = athen p (ainv p g) (athen p (ainv p f) (1, 0)) := by
      rw [athen_one_right, ainv_athen p f g hf hg]
    rw [e]; exact key
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have hg := Walk.label_unit p hp5 hw
    have hfi : (ainv p f).1 ≠ 0 := by
      simp only [ainv]; exact inv_ne_zero hf
    have key := Walk.append p ih (Walk.fwd he (Walk.nil w))
    have e : ainv p (athen p (ainv p f) g)
        = athen p (ainv p g) (athen p f (1, 0)) := by
      rw [athen_one_right, ainv_athen p (ainv p f) g hfi hg, ainv_ainv p f hf]
    rw [e]; exact key

theorem Hol_mul {K : ℕ} {f g : Aff p}
    (hf : f ∈ Hol p K) (hg : g ∈ Hol p K) : athen p f g ∈ Hol p K := Walk.append p hf hg

theorem Hol_inv (hp5 : 5 ≤ p) {K : ℕ} {f : Aff p}
    (hf : f ∈ Hol p K) : ainv p f ∈ Hol p K := Walk.symm p hp5 hf

/-! ## Walks act on stabilised fibres -/

/-- Each edge maps its source fibre onto its target fibre once stabilised. -/
theorem edge_image (hp5 : 5 ≤ p) {v K0 K : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (hS : Stab p v K0) (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : ℕ × ℕ} {f : Aff p}
    (h : Edge p K u w f) :
    (aapp p f) '' (fibre p K v u.1 u.2) = fibre p K v w.1 w.2 := by
  cases h with
  | @D c f0 hc hlt hf0 =>
    show (aapp p ((2 : ZMod p), 0)) '' fibre p K v c f0 = fibre p K v ((2 * c) % 3 ^ (K + 1)) 0
    have h1 : fibre p K v c f0 = fibre p K v c 0 := by
      interval_cases f0
      · rfl
      · exact (hS K hK hK1).1 c hc hlt
    have hfun : aapp p ((2 : ZMod p), 0) = fun t => 2 * t := by
      funext t; simp [aapp]
    rw [h1, fibre_D_eq p hp5 hK1 hc hlt, hfun]
  | @U e h1 h9 hlt =>
    have hM : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by ring
    have hM2 : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := by ring
    have ht0 : ((e - 1) / 3) % 3 ^ (K + 1) = (e - 1) / 3 :=
      Nat.mod_eq_of_lt (by omega)
    have hSb := (hS K hK hK1).2 e (by omega) hlt
    show (aapp p (((3 : ZMod p))⁻¹, -((3 : ZMod p))⁻¹)) '' fibre p K v (e % 3 ^ (K + 1)) 0
        = fibre p K v (((e - 1) / 3) % 3 ^ (K + 1)) 1
    rw [ht0, ← hSb]
    have he0 : (3 * ((e - 1) / 3) + 1) % 3 ^ (K + 1 + 1) = e := by
      rw [show 3 * ((e - 1) / 3) + 1 = e by omega]
      exact Nat.mod_eq_of_lt (by omega)
    have h3 := three_ne_zero_zmod p hp5
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [fibre_U_iff p hp5 hv hv3 (t0 := (e - 1) / 3) (by omega) (by omega), he0]
      have : 3 * (aapp p (((3 : ZMod p))⁻¹, -((3 : ZMod p))⁻¹) t) + 1 = t := by
        simp only [aapp]; field_simp; ring
      rw [this]; exact ht
    · intro ha
      rw [fibre_U_iff p hp5 hv hv3 (t0 := (e - 1) / 3) (by omega) (by omega), he0] at ha
      refine ⟨3 * a + 1, ha, ?_⟩
      simp only [aapp]; field_simp; ring

theorem walk_image (hp5 : 5 ≤ p) {v K0 K : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (hS : Stab p v K0) (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : ℕ × ℕ} {f : Aff p}
    (h : Walk p K u w f) :
    (aapp p f) '' (fibre p K v u.1 u.2) = fibre p K v w.1 w.2 := by
  induction h with
  | nil c => ext t; simp [aapp]
  | @fwd u w d f g he hw ih =>
    have e1 := edge_image p hp5 hv hv3 hS hK hK1 he
    have hfun : aapp p (athen p f g) = aapp p g ∘ aapp p f := funext (athen_app p f g)
    rw [hfun, Set.image_comp, e1, ih]
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have e1 := edge_image p hp5 hv hv3 hS hK hK1 he
    have e2 : (aapp p (ainv p f)) '' (fibre p K v w.1 w.2) = fibre p K v u.1 u.2 := by
      rw [← e1, ← Set.image_comp]
      have : aapp p (ainv p f) ∘ aapp p f = id := funext (ainv_app p f hf)
      rw [this, Set.image_id]
    have hfun : aapp p (athen p (ainv p f) g) = aapp p g ∘ aapp p (ainv p f) :=
      funext (athen_app p (ainv p f) g)
    rw [hfun, Set.image_comp, e2, ih]

/-! ## No flat assignment -/

def Flat (K : ℕ) (Φ : ℕ × ℕ → ZMod p) : Prop :=
  ∀ u w f, Edge p K u w f → Φ w = aapp p f (Φ u)

theorem flat_collapse (hp5 : 5 ≤ p) {K : ℕ} {Φ : ℕ × ℕ → ZMod p} (hΦ : Flat p K Φ)
    {c : ℕ} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) : Φ (c, 0) = Φ (c, 1) := by
  have h0 := hΦ _ _ _ (Edge.D (p := p) (f := 0) hc hlt (by norm_num))
  have h1 := hΦ _ _ _ (Edge.D (p := p) (f := 1) hc hlt (by norm_num))
  have e : (2 : ZMod p) * Φ (c, 0) = 2 * Φ (c, 1) := by
    have := h0.symm.trans h1
    simpa [aapp] using this
  exact mul_left_cancel₀ (two_ne_zero_zmod p hp5) e

theorem flat_double (_hp5 : 5 ≤ p) {K : ℕ} {Φ : ℕ × ℕ → ZMod p} (hΦ : Flat p K Φ)
    {c : ℕ} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) :
    Φ ((2 * c) % 3 ^ (K + 1), 0) = 2 * Φ (c, 0) := by
  have h0 := hΦ _ _ _ (Edge.D (p := p) (f := 0) hc hlt (by norm_num))
  simpa [aapp] using h0

/-- Normalisation Φ(1) = 1, via the U-edge at e = 4 plus two D-steps. -/
theorem flat_one (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) : Φ (1, 0) = 1 := by
  have h3 := three_ne_zero_zmod p hp5
  have hM : 9 ≤ 3 ^ (K + 1) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM2 : 3 ^ (K + 1) ≤ 3 ^ (K + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e0 := hΦ _ _ _ (Edge.U (p := p) (K := K) (e := 4) (by norm_num) (by norm_num)
    (by omega))
  have h4 : 4 % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  have h1m : 1 % 3 ^ (K + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hc : (4 - 1) / 3 = 1 := by norm_num
  rw [hc, h1m, h4] at e0
  have d1 := flat_double p hp5 hΦ (c := 1) (by norm_num) (by omega)
  have d2 := flat_double p hp5 hΦ (c := 2) (by norm_num) (by omega)
  have m2 : (2 * 1) % 3 ^ (K + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  have m4 : (2 * 2) % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  rw [m2] at d1
  rw [m4] at d2
  have hcol := flat_collapse p hp5 hΦ (c := 1) (by norm_num) (by omega)
  have e1 : Φ (1, 1) = (3 : ZMod p)⁻¹ * Φ (4, 0) + -(3 : ZMod p)⁻¹ := by
    simpa [aapp] using e0
  rw [← hcol, d2, d1] at e1
  have key : (3 : ZMod p) * 3⁻¹ = 1 := mul_inv_cancel₀ h3
  linear_combination (-3) * e1 - (4 * Φ (1, 0) - 1) * key

/-- Φ(2^j mod 3^(K+1)) = 2^j. -/
theorem flat_hom (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) :
    ∀ j : ℕ, Φ ((2 ^ j) % 3 ^ (K + 1), 0) = (2 : ZMod p) ^ j := by
  intro j
  induction j with
  | zero =>
    rw [pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)]
    simpa using flat_one p hp5 hK hΦ
  | succ j ih =>
    have hc : (2 ^ j % 3 ^ (K + 1)) % 3 ≠ 0 :=
      mod_unit (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt : 2 ^ j % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
    have h1 := flat_double p hp5 hΦ hc hlt
    rw [ih] at h1
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      rw [Nat.mul_mod_mod, pow_succ 2 j, mul_comm 2 (2 ^ j)]
    rw [e] at h1
    rw [h1, pow_succ]; ring

theorem two_pow_N (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) : (2 : ZMod p) ^ (2 * 3 ^ K) = 1 := by
  have h := flat_hom p hp5 hK hΦ (2 * 3 ^ K)
  have hN : 2 ^ (2 * 3 ^ K) % 3 ^ (K + 1) = 1 := by
    have := (two_pow_modEq_one_iff (K := K) (m := 2 * 3 ^ K)).2 dvd_rfl
    unfold Nat.ModEq at this
    rw [this]; exact Nat.mod_eq_of_lt (one_lt_pow3 K)
  rw [hN, flat_one p hp5 hK hΦ] at h
  exact h.symm

/-- Cubing a principal unit raises the 3-adic level by one:
(1 + 3^j u)^(3^n) = 1 + 3^(j+n) w with 3 ∤ w. -/
lemma pow3_form {j u : ℕ} (hj : 1 ≤ j) (hu : u % 3 ≠ 0) :
    ∀ n : ℕ, ∃ w : ℕ, w % 3 ≠ 0 ∧ (1 + 3 ^ j * u) ^ (3 ^ n) = 1 + 3 ^ (j + n) * w := by
  intro n
  induction n with
  | zero => exact ⟨u, hu, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, hx⟩ := ih
    obtain ⟨k', hk'⟩ : ∃ k', j + n = k' + 1 := ⟨j + n - 1, by omega⟩
    refine ⟨w + 3 ^ (k' + 1) * w ^ 2 + 3 ^ (2 * k' + 1) * w ^ 3, ?_, ?_⟩
    · have e : w + 3 ^ (k' + 1) * w ^ 2 + 3 ^ (2 * k' + 1) * w ^ 3
          = w + 3 * (3 ^ k' * w ^ 2 + 3 ^ (2 * k') * w ^ 3) := by ring
      rw [e]
      generalize (3 ^ k' * w ^ 2 + 3 ^ (2 * k') * w ^ 3) = A
      omega
    · rw [pow_succ, pow_mul, hx, hk']
      have e2 : j + (n + 1) = k' + 2 := by omega
      rw [e2]; ring

/-- The principal-unit order ord_{3^(K+1)}(1 + 3^j u) = 3^(K+1-j).
Proved via `orderOf_eq_prime_pow` and `pow3_form`; not used by the main chain. -/
theorem principal_order {K j u : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) (hu : u % 3 ≠ 0) :
    orderOf ((1 + 3 ^ j * u : ℕ) : ZMod (3 ^ (K + 1))) = 3 ^ (K + 1 - j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hm : K + 1 - j = (K - j) + 1 := by omega
  rw [hm]
  apply orderOf_eq_prime_pow (p := 3) (n := K - j)
  · intro h
    obtain ⟨w, hw, hx⟩ := pow3_form hj hu (K - j)
    have hjn : j + (K - j) = K := by omega
    rw [hjn] at hx
    have h' : (((1 + 3 ^ j * u) ^ (3 ^ (K - j)) : ℕ) : ZMod (3 ^ (K + 1))) = 1 := by
      rw [Nat.cast_pow]; exact h
    rw [hx] at h'
    have h0 : ((3 ^ K * w : ℕ) : ZMod (3 ^ (K + 1))) = 0 := by
      push_cast at h' ⊢
      linear_combination h'
    have hdv : 3 ^ (K + 1) ∣ 3 ^ K * w :=
      (CharP.cast_eq_zero_iff (ZMod (3 ^ (K + 1))) (3 ^ (K + 1)) _).1 h0
    rw [pow_succ] at hdv
    have h3w : 3 ∣ w := Nat.dvd_of_mul_dvd_mul_left (by positivity) hdv
    omega
  · obtain ⟨w, hw, hx⟩ := pow3_form hj hu (K - j + 1)
    have hjn : j + (K - j + 1) = K + 1 := by omega
    rw [hjn] at hx
    have hz : ((3 ^ (K + 1) : ℕ) : ZMod (3 ^ (K + 1))) = 0 := ZMod.natCast_self _
    have h' : (((1 + 3 ^ j * u) ^ (3 ^ (K - j + 1)) : ℕ) : ZMod (3 ^ (K + 1))) = 1 := by
      rw [hx, Nat.cast_add, Nat.cast_mul, hz, zero_mul, add_zero, Nat.cast_one]
    rw [Nat.cast_pow] at h'
    exact h'

/-- The U-edge relation in additive form: 3 Φ(target) = Φ(source) - 1. -/
theorem flat_U (hp5 : 5 ≤ p) {K : ℕ} {Φ : ℕ × ℕ → ZMod p} (hΦ : Flat p K Φ)
    {e : ℕ} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
    3 * Φ (((e - 1) / 3) % 3 ^ (K + 1), 1) = Φ (e % 3 ^ (K + 1), 0) - 1 := by
  have he := hΦ _ _ _ (Edge.U (p := p) (K := K) (e := e) h1 h9 hlt)
  have e1 : Φ (((e - 1) / 3) % 3 ^ (K + 1), 1)
      = (3 : ZMod p)⁻¹ * Φ (e % 3 ^ (K + 1), 0) + -(3 : ZMod p)⁻¹ := by
    exact he
  have key : (3 : ZMod p) * 3⁻¹ = 1 := mul_inv_cancel₀ (three_ne_zero_zmod p hp5)
  rw [e1]
  linear_combination (Φ (e % 3 ^ (K + 1), 0) - 1) * key

/-- Every unit ≡ 1 (mod 3) is a power of 4 modulo 3^(K+1), and Φ is 4^e there. -/
theorem flat_four_form (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) {c : ℕ} (hc : c % 3 = 1) (hlt : c < 3 ^ (K + 1)) :
    ∃ e : ℕ, (4 ^ e) % 3 ^ (K + 1) = c ∧ Φ (c, 0) = (4 : ZMod p) ^ e := by
  obtain ⟨j, hj⟩ := two_transitive hK (c := 1) (d := c) (by norm_num) (by omega) hlt
  rw [mul_one] at hj
  have hjev : j % 2 = 0 := by
    by_contra hodd
    obtain ⟨i, rfl⟩ : ∃ i, j = 2 * i + 1 := ⟨j / 2, by omega⟩
    have e : 2 ^ (2 * i + 1) = 2 * 4 ^ i := by
      rw [pow_succ, pow_mul]; norm_num; try ring
    have hm : c % 3 = 2 ^ (2 * i + 1) % 3 := by
      rw [← hj, Nat.mod_mod_of_dvd _ (three_dvd_pow K)]
    rw [e] at hm
    have h4 := four_pow_mod_three i
    omega
  obtain ⟨e, rfl⟩ : ∃ e, j = 2 * e := ⟨j / 2, by omega⟩
  have h4e : (2 : ℕ) ^ (2 * e) = 4 ^ e := by rw [pow_mul]; norm_num
  refine ⟨e, by rw [← h4e]; exact hj, ?_⟩
  have hf := flat_hom p hp5 hK hΦ (2 * e)
  rw [hj] at hf
  rw [hf, pow_mul]; norm_num

/-- Steps 4–5: the self-target y = (3^(K+1)-1)/2, lifted by v = 1, 2, gives
φ(y + 3^K) = φ(y); with `four_pow_cong` and `flat_hom`, 4^(3^(K-1)) = 1 in ZMod p. -/
theorem flat_four_pow (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) : (4 : ZMod p) ^ (3 ^ (K - 1)) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  have hsub : n + 1 - 1 = n := by omega
  rw [hsub]
  obtain ⟨s, hs⟩ : ∃ s, s = 3 ^ n := ⟨_, rfl⟩
  rw [← hs]
  have hMs : 3 ^ (n + 1 + 1) = 9 * s := by rw [hs]; ring
  have hKs : 3 ^ (n + 1) = 3 * s := by rw [hs]; ring
  have h3K2 : 3 ^ (n + 1 + 2) = 27 * s := by rw [hs]; ring
  have hspos : 0 < s := by rw [hs]; positivity
  have hsodd : s % 2 = 1 := by
    rw [hs]; exact Nat.odd_iff.mp (Odd.pow ⟨1, by norm_num⟩)
  have h3 := three_ne_zero_zmod p hp5
  -- base-4 congruence
  have hc4 := four_pow_cong (K := n + 1) (by omega)
  rw [hsub, ← hs, hMs, hKs] at hc4
  have h4' : 4 ^ s % (9 * s) = 1 + 3 * s := by
    rw [hc4]; exact Nat.mod_eq_of_lt (by omega)
  -- the self-target y
  obtain ⟨y, hy⟩ : ∃ y, 2 * y + 1 = 9 * s := ⟨(9 * s - 1) / 2, by omega⟩
  have hy_lt : y < 9 * s := by omega
  have hy3 : y % 3 = 1 := by omega
  have hy9 : y % 9 = 4 := by omega
  have hcy := flat_collapse p hp5 hΦ (c := y) (by omega) (by rw [hMs]; exact hy_lt)
  have m0 : y % 3 ^ (n + 1 + 1) = y := by rw [hMs]; exact Nat.mod_eq_of_lt hy_lt
  -- lift s = 1
  have u1 := flat_U p hp5 hΦ (e := y + 9 * s) (by omega) (by omega) (by rw [h3K2]; omega)
  have t1 : (y + 9 * s - 1) / 3 = y := by omega
  have m1 : (y + 9 * s) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mod_right, Nat.mod_eq_of_lt hy_lt]
  rw [t1, m0, m1] at u1
  -- lift s = 2
  have u2 := flat_U p hp5 hΦ (e := y + 9 * s * 2) (by omega) (by omega) (by rw [h3K2]; omega)
  have t2 : (y + 9 * s * 2 - 1) / 3 = y + 3 * s := by omega
  have hy3s : y + 3 * s < 9 * s := by omega
  have m3 : (y + 3 * s) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    rw [hMs]; exact Nat.mod_eq_of_lt hy3s
  have m2 : (y + 9 * s * 2) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy_lt]
  rw [t2, m3, m2] at u2
  have hcy2 := flat_collapse p hp5 hΦ (c := y + 3 * s) (by omega) (by rw [hMs]; exact hy3s)
  have hA : 3 * Φ (y, 0) = Φ (y, 0) - 1 := by linear_combination 3 * hcy + u1
  have hB : Φ (y + 3 * s, 1) = Φ (y, 0) :=
    mul_left_cancel₀ h3 (by linear_combination u2 - hA)
  have hC0 : Φ (y + 3 * s, 0) = Φ (y, 0) := hcy2.trans hB
  -- express y and y + 3s as powers of 2
  obtain ⟨j, hj⟩ := two_transitive (K := n + 1) (c := 1) (d := y) (by omega)
    (by norm_num) (by omega) (by rw [hMs]; exact hy_lt)
  rw [mul_one] at hj
  have hfy := flat_hom p hp5 (K := n + 1) (by omega) hΦ j
  rw [hj] at hfy
  have hj' : 2 ^ j % (9 * s) = y := by rw [← hMs]; exact hj
  have hmod : (2 ^ (j + 2 * s)) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    have e : 2 ^ (j + 2 * s) = 2 ^ j * 4 ^ s := by
      rw [pow_add, pow_mul]; norm_num
    obtain ⟨m, hm⟩ : ∃ m, y = 3 * m + 1 := ⟨y / 3, by omega⟩
    have hprod : y * (1 + 3 * s) = (y + 3 * s) + 9 * s * m := by
      rw [hm]; ring
    rw [hMs, e, Nat.mul_mod, hj', h4', hprod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hy3s]
  have hf2 := flat_hom p hp5 (K := n + 1) (by omega) hΦ (j + 2 * s)
  rw [hmod] at hf2
  have hpow : (2 : ZMod p) ^ (j + 2 * s) = 2 ^ j := hf2.symm.trans (hC0.trans hfy)
  have h2 : (2 : ZMod p) ^ j * 2 ^ (2 * s) = 2 ^ j * 1 := by
    rw [← pow_add, mul_one]; exact hpow
  have h2' := mul_left_cancel₀ (pow_ne_zero j (two_ne_zero_zmod p hp5)) h2
  have e4 : (4 : ZMod p) = 2 ^ 2 := by norm_num
  rw [e4, ← pow_mul]
  exact h2'

/-- Step 6.  ord_p 4 = 3^a (1 ≤ a ≤ K-1); coupled nodes 4 and 4 + 3^(a+1);
contradiction via `four_pow_modEq_one_iff`. -/
theorem flat_contra (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {Φ : ℕ × ℕ → ZMod p}
    (hΦ : Flat p K Φ) (h4 : (4 : ZMod p) ^ (3 ^ (K - 1)) = 1) : False := by
  have h3 := three_ne_zero_zmod p hp5
  have hdvd : orderOf (4 : ZMod p) ∣ 3 ^ (K - 1) := orderOf_dvd_of_pow_eq_one h4
  obtain ⟨a, haK, hord⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hk : ∀ m : ℕ, (4 : ZMod p) ^ m = 1 ↔ 3 ^ a ∣ m := by
    intro m; rw [← hord, orderOf_dvd_iff_pow_eq_one]
  have ha1 : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    subst ha0
    have h1 : (4 : ZMod p) ^ 1 = 1 := (hk 1).2 (by simp)
    rw [pow_one] at h1
    have h30 : (3 : ZMod p) = 0 := by linear_combination h1
    exact h3 h30
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, r = 3 ^ a' := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = 3 ^ K := ⟨_, rfl⟩
  have hq2 : 3 ^ (a' + 1 + 1) = 9 * r := by rw [hr]; ring
  have hrpos : 0 < r := by rw [hr]; positivity
  have hle : 3 ^ (a' + 1 + 1) ≤ 3 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hq2, ← hR] at hle
  have hM : 3 ^ (K + 1) = 3 * R := by rw [hR]; ring
  have hM2 : 3 ^ (K + 2) = 9 * R := by rw [hR]; ring
  have hdv : 3 ^ (a' + 1 + 1) ∣ 3 ^ (K + 1) := pow_dvd_pow 3 (by omega)
  have hcop4 : Nat.gcd (3 ^ (a' + 1 + 1)) 4 = 1 :=
    Nat.Coprime.pow_left (a' + 1 + 1) (by norm_num : Nat.Coprime 3 4)
  -- node c₂ = 4 + 3^(a+1) = 4 + 9r : Φ(c₂) = 4
  have hc2lt : 4 + 9 * r < 3 ^ (K + 1) := by rw [hM]; omega
  obtain ⟨e, he, hΦe⟩ := flat_four_form p hp5 hK hΦ (c := 4 + 9 * r) (by omega) hc2lt
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    rw [he0, pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)] at he
    omega
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hmod1 : 4 ^ (e' + 1) ≡ 4 + 9 * r [MOD 3 ^ (K + 1)] := by
    unfold Nat.ModEq; rw [he, Nat.mod_eq_of_lt hc2lt]
  have hm1 := Nat.ModEq.of_dvd hdv hmod1
  have hm2 : 4 ^ (e' + 1) ≡ 4 [MOD 3 ^ (a' + 1 + 1)] := by
    unfold Nat.ModEq at hm1 ⊢
    rw [hm1, hq2, Nat.add_mod_right]
  have hm3 : 4 * 4 ^ e' ≡ 4 * 1 [MOD 3 ^ (a' + 1 + 1)] := by
    rw [mul_one, ← pow_succ']; exact hm2
  have hm4 := Nat.ModEq.cancel_left_of_coprime hcop4 hm3
  have hd1 : 3 ^ (a' + 1) ∣ e' := (four_pow_modEq_one_iff (K := a' + 1) (m := e')).1 hm4
  have hφ2 : Φ (4 + 9 * r, 0) = 4 := by
    rw [hΦe, pow_succ, (hk e').2 hd1, one_mul]
  -- U-edge from c₂ gives Φ(1 + 3r, 1) = 1
  have ub := flat_U p hp5 hΦ (e := 4 + 9 * r) (by omega) (by omega) (by rw [hM2]; omega)
  have tb : (4 + 9 * r - 1) / 3 = 1 + 3 * r := by omega
  have mb1 : (1 + 3 * r) % 3 ^ (K + 1) = 1 + 3 * r :=
    Nat.mod_eq_of_lt (by rw [hM]; omega)
  have mb2 : (4 + 9 * r) % 3 ^ (K + 1) = 4 + 9 * r := Nat.mod_eq_of_lt hc2lt
  rw [tb, mb1, mb2, hφ2] at ub
  have hΦ1 : Φ (1 + 3 * r, 1) = 1 := mul_left_cancel₀ h3 (by linear_combination ub)
  have hcol := flat_collapse p hp5 hΦ (c := 1 + 3 * r) (by omega) (by rw [hM]; omega)
  have hone : Φ (1 + 3 * r, 0) = 1 := hcol.trans hΦ1
  -- the target 1 + 3^a is a power of 4 with Φ = 1, forcing 3^a ∣ exponent, hence ≡ 1 mod 3^(a+1)
  obtain ⟨d, hd, hΦd⟩ := flat_four_form p hp5 hK hΦ (c := 1 + 3 * r) (by omega)
    (by rw [hM]; omega)
  have hpd : (4 : ZMod p) ^ d = 1 := hΦd.symm.trans hone
  have hdd : 3 ^ (a' + 1) ∣ d := (hk d).1 hpd
  have hmodd : 4 ^ d ≡ 1 [MOD 3 ^ (a' + 1 + 1)] :=
    (four_pow_modEq_one_iff (K := a' + 1) (m := d)).2 hdd
  have h5 := Nat.mod_mod_of_dvd (4 ^ d) hdv
  rw [hd] at h5
  unfold Nat.ModEq at hmodd
  rw [hq2] at h5 hmodd
  have l1 : 1 + 3 * r < 9 * r := by omega
  have l2 : 1 < 9 * r := by omega
  rw [Nat.mod_eq_of_lt l1] at h5
  rw [Nat.mod_eq_of_lt l2] at hmodd
  omega

theorem no_flat (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    ¬ ∃ Φ : ℕ × ℕ → ZMod p, Flat p K Φ := by
  rintro ⟨Φ, hΦ⟩
  exact flat_contra p hp5 hK hΦ (flat_four_pow p hp5 hK hΦ)

/-! ## From a flat-assignment obstruction to a translation -/

theorem walk_two_pow {K : ℕ} (_hK : 1 ≤ K) :
    ∀ j : ℕ, ∃ g : Aff p, Walk p K base ((2 ^ j) % 3 ^ (K + 1), 0) g := by
  intro j
  induction j with
  | zero =>
    rw [pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)]
    exact ⟨_, Walk.nil base⟩
  | succ j ih =>
    obtain ⟨g, hg⟩ := ih
    have hc := mod_unit (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt := Nat.mod_lt (2 ^ j) (show 0 < 3 ^ (K + 1) by positivity)
    have he := Edge.D (p := p) (K := K) (f := 0) hc hlt (by norm_num)
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      rw [Nat.mul_mod_mod, pow_succ 2 j, mul_comm 2 (2 ^ j)]
    rw [e] at he
    exact ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil _))⟩

theorem connected_even {K : ℕ} (hK : 1 ≤ K) {c : ℕ} (hc : c % 3 ≠ 0)
    (hlt : c < 3 ^ (K + 1)) : ∃ g : Aff p, Walk p K base (c, 0) g := by
  obtain ⟨j, hj⟩ := two_transitive hK (c := 1) (d := c) (by norm_num) hc hlt
  rw [mul_one] at hj
  obtain ⟨g, hg⟩ := walk_two_pow p hK j
  rw [hj] at hg
  exact ⟨g, hg⟩

/-- Every valid state is joined to `base`. -/
theorem connected {K : ℕ} (hK : 1 ≤ K) {c f : ℕ}
    (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
    ∃ g : Aff p, Walk p K base (c, f) g := by
  interval_cases f
  · exact connected_even p hK hc hlt
  · have hM : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := by ring
    have h1 : (3 * c + 1) % 3 = 1 := by omega
    have h9 : (3 * c + 1) % 9 ≠ 1 := by omega
    have hlt2 : 3 * c + 1 < 3 ^ (K + 2) := by omega
    have he := Edge.U (p := p) (K := K) (e := 3 * c + 1) h1 h9 hlt2
    have h3c : (3 * c + 1 - 1) / 3 = c := by omega
    rw [h3c, Nat.mod_eq_of_lt hlt] at he
    have hsrc : (3 * c + 1) % 3 ^ (K + 1) % 3 ≠ 0 :=
      mod_unit (three_dvd_pow K) (by omega)
    obtain ⟨g, hg⟩ := connected_even p hK hsrc (Nat.mod_lt _ (by positivity))
    exact ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil _))⟩

/-- A common fixed point of `Hol` yields a flat assignment. -/
theorem flat_of_fixed (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) (x : ZMod p)
    (hx : ∀ f ∈ Hol p K, aapp p f x = x) : ∃ Φ : ℕ × ℕ → ZMod p, Flat p K Φ := by
  classical
  have hval : ∀ {u : ℕ × ℕ} {g1 g2 : Aff p}, Walk p K base u g1 → Walk p K base u g2 →
      aapp p g1 x = aapp p g2 x := by
    intro u g1 g2 h1 h2
    have hh : athen p g1 (ainv p g2) ∈ Hol p K := Walk.append p h1 (Walk.symm p hp5 h2)
    have hfix := hx _ hh
    rw [athen_app] at hfix
    have hu := Walk.label_unit p hp5 h2
    have hinv : ∀ z, aapp p g2 (aapp p (ainv p g2) z) = z := by
      intro z
      have hi : (ainv p g2).1 ≠ 0 := by simpa [ainv] using inv_ne_zero hu
      have := ainv_app p (ainv p g2) hi z
      rwa [ainv_ainv p g2 hu] at this
    have := congrArg (aapp p g2) hfix
    rw [hinv] at this
    exact this
  refine ⟨fun u => if h : ∃ g, Walk p K base u g then aapp p h.choose x else 0, ?_⟩
  rintro ⟨c, f0⟩ w f he
  obtain ⟨hc, hlt, hf⟩ := Edge.src_valid p he
  obtain ⟨g, hg⟩ := connected p hK hc hlt hf
  have hu : ∃ g, Walk p K base (c, f0) g := ⟨g, hg⟩
  have hw : ∃ g', Walk p K base w g' :=
    ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil w))⟩
  dsimp only
  rw [dite_eq_left hw, dite_eq_left hu]
  have e1 := hval (Classical.choose_spec hw)
    (Walk.append p hg (Walk.fwd he (Walk.nil w)))
  have e2 := hval (Classical.choose_spec hu) hg
  rw [e1, e2, athen_app, athen_app]
  simp [aapp]

/-- `Hol` with no common fixed point contains a nonzero translation
(a commutator of a slope ≠ 1 element with one that moves its fixed point). -/
theorem translation_of_no_fixed (hp5 : 5 ≤ p) {K : ℕ}
    (hno : ¬ ∃ x : ZMod p, ∀ f ∈ Hol p K, aapp p f x = x) : HasTranslation p K := by
  by_contra hnt
  apply hno
  by_cases hall : ∀ f ∈ Hol p K, f.1 = 1
  · refine ⟨0, fun f hf => ?_⟩
    have h1 := hall f hf
    by_contra hne
    apply hnt
    refine ⟨f.2, fun h => hne (by simp [aapp, h]), ?_⟩
    have : f = (1, f.2) := Prod.ext h1 rfl
    rw [← this]; exact hf
  · push Not at hall
    obtain ⟨h0, hh0, hl1⟩ := hall
    obtain ⟨l0, m0⟩ := h0
    have hl1' : l0 ≠ 1 := hl1
    have hh0' : Walk p K base base (l0, m0) := hh0
    have hl0 : l0 ≠ 0 := Walk.label_unit p hp5 hh0'
    obtain ⟨x0, hx0⟩ : ∃ x0, x0 * (1 - l0) = m0 :=
      ⟨m0 / (1 - l0), by
        have : 1 - l0 ≠ 0 := sub_ne_zero.2 (Ne.symm hl1')
        field_simp⟩
    subst hx0
    refine ⟨x0, fun k hk => ?_⟩
    obtain ⟨lk, mk⟩ := k
    have hk' : Walk p K base base (lk, mk) := hk
    have hlk : lk ≠ 0 := Walk.label_unit p hp5 hk'
    have hg : athen p (athen p (athen p (lk, mk) (l0, x0 * (1 - l0))) (ainv p (lk, mk)))
        (ainv p (l0, x0 * (1 - l0))) ∈ Hol p K :=
      Hol_mul p (Hol_mul p (Hol_mul p hk hh0) (Hol_inv p hp5 hk)) (Hol_inv p hp5 hh0)
    have hform : athen p (athen p (athen p (lk, mk) (l0, x0 * (1 - l0))) (ainv p (lk, mk)))
        (ainv p (l0, x0 * (1 - l0)))
        = (1, (l0 - 1) * (lk * x0 + mk - x0) / (lk * l0)) := by
      apply Prod.ext
      · simp only [athen, ainv]; field_simp
      · simp only [athen, ainv]; field_simp; try ring
    rw [hform] at hg
    by_cases hd : (l0 - 1) * (lk * x0 + mk - x0) / (lk * l0) = 0
    · have hnum : (l0 - 1) * (lk * x0 + mk - x0) = 0 := by
        rcases div_eq_zero_iff.1 hd with h | h
        · exact h
        · exact absurd h (mul_ne_zero hlk hl0)
      rcases mul_eq_zero.1 hnum with h | h
      · exact absurd (sub_eq_zero.1 h) hl1'
      · show lk * x0 + mk = x0
        linear_combination h
    · exact absurd ⟨_, hd, hg⟩ hnt

theorem translation_exists (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) : HasTranslation p K := by
  apply translation_of_no_fixed p hp5
  rintro ⟨x, hx⟩
  obtain ⟨Φ, hΦ⟩ := flat_of_fixed p hp5 hK x hx
  exact no_flat p hp5 hK ⟨Φ, hΦ⟩

/-! ## Simultaneous density -/

theorem main_theorem_core (hp5 : 5 ≤ p) {v : ℕ} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    {J : ℕ} (hJ : 1 ≤ J) {c : ℕ} (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (J + 1)) (r : ZMod p) :
    ∃ n, Tree v n ∧ n % 3 ^ (J + 1) = c ∧ (n : ZMod p) = r := by
  obtain ⟨K0, hK0, hS⟩ := stabilization p hp5 hv hv3
  set K := max (max K0 J) 1 with hKdef
  have hKK0 : K0 ≤ K := by omega
  have hKJ : J ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  obtain ⟨d, hd0, hd⟩ := translation_exists p hp5 hK1
  have himg := walk_image p hp5 hv hv3 hS hKK0 hK1 hd
  have hbase : (aapp p (1, d)) '' (fibre p K v 1 0) = fibre p K v 1 0 := himg
  obtain ⟨t0, ht0⟩ : (fibre p K v 1 0).Nonempty := by
    have := sig_pos p hp5 hv hv3 K hK1
    unfold sig at this
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  have step : ∀ t ∈ fibre p K v 1 0, t + d ∈ fibre p K v 1 0 := by
    intro t ht
    have h1 : aapp p (1, d) t ∈ (aapp p (1, d)) '' fibre p K v 1 0 := ⟨t, ht, rfl⟩
    rw [hbase] at h1
    simpa [aapp] using h1
  have key : ∀ k : ℕ, t0 + (k : ZMod p) * d ∈ fibre p K v 1 0 := by
    intro k
    induction k with
    | zero => simpa using ht0
    | succ k ih =>
      have := step _ ih
      convert this using 1
      push_cast; ring
  have hfull : fibre p K v 1 0 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro r'
    have := key ((r' - t0) / d).val
    rw [ZMod.natCast_zmod_val] at this
    have e : t0 + (r' - t0) / d * d = r' := by field_simp; ring
    rwa [e] at this
  have hcK : c < 3 ^ (K + 1) :=
    lt_of_lt_of_le hcl (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hfullc : fibre p K v c 0 = Set.univ := by
    have hcc := fibre_card_const p hp5 (v := v) hK1 (c := 1) (d := c)
      (by norm_num) (one_lt_pow3 K) hc hcK
    rw [hfull, Set.ncard_univ] at hcc
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ]; omega)
  have hr : r ∈ fibre p K v c 0 := by rw [hfullc]; trivial
  have hr' := fibre_proj p hKJ hr
  have hcmod : c % 3 ^ (J + 1) = c := Nat.mod_eq_of_lt hcl
  rw [hcmod] at hr'
  obtain ⟨n, hn, hn1, _, hn3⟩ := hr'
  exact ⟨n, hn, hn1, hn3⟩

/-! ## The three cases and the master theorem -/

lemma cast_eq_of_mod {p : ℕ} [Fact p.Prime] {n : ℕ} {r : ZMod p} (h : n % p = r.val) :
    (n : ZMod p) = r := by
  rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]

lemma cast_eq_of_mod' {p q : ℕ} [Fact p.Prime] (hpq : p = q) {n : ℕ} {r : ZMod p}
    (h : n % q = r.val) : (n : ZMod p) = r := by
  apply cast_eq_of_mod
  have : n % p = n % q := by rw [hpq]
  rw [this]; exact h

lemma sixtyfour_pow_mod (t : ℕ) : 64 ^ t % 9 = 1 := by
  induction t with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma lt_pow_mul {B k w : ℕ} (hk : B ≤ k) (hw : 0 < w) : B < 2 ^ k * w := by
  have h1 : k < 2 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ k ≤ 2 ^ k * w := Nat.le_mul_of_pos_right _ hw
  omega

lemma exists_pow_two_mod (w a : ℕ) (hw3 : w % 3 ≠ 0) (ha9 : a = 1 ∨ a = 2) :
    ∃ j < 6, 2 ^ j * w % 9 = a := by
  have hm9 : w % 9 = 1 ∨ w % 9 = 2 ∨ w % 9 = 4 ∨ w % 9 = 5 ∨ w % 9 = 7 ∨ w % 9 = 8 := by omega
  rcases ha9 with rfl | rfl
  · rcases hm9 with h | h | h | h | h | h
    · exact ⟨0, by omega, by simp [h]⟩
    · exact ⟨5, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨4, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨1, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨2, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨3, by omega, by norm_num [Nat.mul_mod, h]⟩
  · rcases hm9 with h | h | h | h | h | h
    · exact ⟨1, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨0, by omega, by simp [h]⟩
    · exact ⟨5, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨2, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨3, by omega, by norm_num [Nat.mul_mod, h]⟩
    · exact ⟨4, by omega, by norm_num [Nat.mul_mod, h]⟩

lemma exists_k_mod_three (w t : ℕ) (hw3 : w % 3 ≠ 0) :
    ∃ k, 2 * t ≤ k ∧ k ≤ 2 * t + 1 ∧ 2 ^ k * w % 3 = 1 := by
  have h4 := four_pow_mod_three t
  have e : 2 ^ (2 * t) = 4 ^ t := by rw [pow_mul]; norm_num
  have hcase : w % 3 = 1 ∨ w % 3 = 2 := by omega
  rcases hcase with h | h
  · refine ⟨2 * t, le_refl _, by omega, ?_⟩
    rw [e]
    have hm := Nat.mul_mod (4 ^ t) w 3
    rw [h4, h] at hm
    omega
  · refine ⟨2 * t + 1, by omega, le_refl _, ?_⟩
    have e3 : 2 ^ (2 * t + 1) * w = 4 ^ t * (2 * w) := by
      rw [pow_succ, e]; ring
    rw [e3]
    have hm := Nat.mul_mod (4 ^ t) (2 * w) 3
    rw [h4] at hm
    omega

lemma odd_of_three_mul_add_one {w k q : ℕ} (hk : 1 ≤ k)
    (hq : 3 * q + 1 = 2 ^ k * w) : q % 2 = 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 ^ (k' + 1) * w = 2 * (2 ^ k' * w) := by ring
  omega

lemma reaches_of_three_mul_add_one {w k q : ℕ} (hk : 1 ≤ k)
    (hq : 3 * q + 1 = 2 ^ k * w) : Reaches w q := by
  have hodd := odd_of_three_mul_add_one hk hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc : collatz q = 2 ^ (k' + 1) * w := by
    unfold collatz
    split_ifs with heven
    · omega
    · exact hq
  refine ⟨k' + 1 + 1, ?_⟩
  rw [Function.iterate_succ_apply, hc]
  exact collatz_pow_mul _ _

lemma exists_large_unit_class (B : ℕ) :
    ∃ J c : ℕ, 1 ≤ J ∧ c % 3 ≠ 0 ∧ c < 3 ^ (J + 1) ∧ B < c := by
  have hpos : 0 < 3 ^ B := by positivity
  refine ⟨B + 1, 9 * 3 ^ B - 1, by omega, by omega, ?_, ?_⟩
  · rw [show 3 ^ (B + 1 + 1) = 9 * 3 ^ B by ring]; omega
  · have hB : B < 3 ^ B := Nat.lt_pow_self (by norm_num)
    omega

theorem main_theorem_p_ge_5 (hp5 : 5 ≤ p) (w : ℕ) (_hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (r : ZMod p) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Reaches w n ∧ (n : ZMod p) = r := by
  obtain ⟨J, c, hJ, hc, hcl, hBc⟩ := exists_large_unit_class B
  have hv : (2 * w) % 2 = 0 := by omega
  have hv3 : (2 * w) % 3 ≠ 0 := by omega
  obtain ⟨n, hn, hnc, hnr⟩ := main_theorem_core p hp5 hv hv3 hJ hc hcl r
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hnc; omega
    · exact h
  have hcn : c ≤ n := by rw [← hnc]; exact Nat.mod_le _ _
  have hsw : Reaches w (2 * w) := ⟨1, by simp [collatz_double]⟩
  exact ⟨n, by omega, reaches_trans (Tree_reaches hn) hsw, hnr⟩

theorem main_theorem_p_eq_2 (w : ℕ) (hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (hp2 : p = 2) (r : ZMod p) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Reaches w n ∧ (n : ZMod p) = r := by
  have hr : r.val < p := ZMod.val_lt r
  have hcase : r.val = 0 ∨ r.val = 1 := by omega
  rcases hcase with h | h
  · refine ⟨2 ^ (B + 1) * w, lt_pow_mul (by omega) hw,
      ⟨B + 1, collatz_pow_mul _ _⟩, ?_⟩
    apply cast_eq_of_mod' hp2
    rw [show 2 ^ (B + 1) * w = 2 * (2 ^ B * w) by ring]
    omega
  · obtain ⟨k, hk1, _hk2, _hk3⟩ := exists_k_mod_three w (3 * B + 3) hw3
    have hbig := lt_pow_mul (B := 6 * B + 6) (k := k) (w := w) (by omega) hw
    have hq : 3 * (2 ^ k * w / 3) + 1 = 2 ^ k * w := by omega
    refine ⟨2 ^ k * w / 3, by omega,
      reaches_of_three_mul_add_one (by omega) hq, ?_⟩
    apply cast_eq_of_mod' hp2
    have := odd_of_three_mul_add_one (by omega : 1 ≤ k) hq
    omega

theorem main_theorem_p_eq_3 (w : ℕ) (hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (hp3 : p = 3) (r : ZMod p) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Reaches w n ∧ (n : ZMod p) = r := by
  have hr : r.val < p := ZMod.val_lt r
  have hcase : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases hcase with h | h | h
  · obtain ⟨j, _, hj⟩ := exists_pow_two_mod w 1 hw3 (Or.inl rfl)
    have h64 : (2 : ℕ) ^ (6 * (B + 1)) = 64 ^ (B + 1) := by
      rw [pow_mul]; norm_num
    have e : 2 ^ (j + 6 * (B + 1)) * w = 64 ^ (B + 1) * (2 ^ j * w) := by
      rw [pow_add, h64]; ring
    have hm := Nat.mul_mod (64 ^ (B + 1)) (2 ^ j * w) 9
    rw [sixtyfour_pow_mod (B + 1), hj] at hm
    have hN : 2 ^ (j + 6 * (B + 1)) * w % 9 = 1 := by rw [e]; omega
    have hq : 3 * (2 ^ (j + 6 * (B + 1)) * w / 3) + 1
        = 2 ^ (j + 6 * (B + 1)) * w := by omega
    have hbig := lt_pow_mul (B := 6 * B + 6) (k := j + 6 * (B + 1)) (w := w)
      (by omega) hw
    refine ⟨2 ^ (j + 6 * (B + 1)) * w / 3, by omega,
      reaches_of_three_mul_add_one (by omega) hq, ?_⟩
    apply cast_eq_of_mod' hp3
    omega
  · obtain ⟨k, _hk1, _hk2, _hk3⟩ := exists_k_mod_three w B hw3
    refine ⟨2 ^ k * w, lt_pow_mul (by omega) hw, ⟨k, collatz_pow_mul _ _⟩, ?_⟩
    apply cast_eq_of_mod' hp3
    omega
  · obtain ⟨k, _hk1, _hk2, _hk3⟩ := exists_k_mod_three w B hw3
    refine ⟨2 ^ (k + 1) * w, lt_pow_mul (by omega) hw,
      ⟨k + 1, collatz_pow_mul _ _⟩, ?_⟩
    apply cast_eq_of_mod' hp3
    rw [show 2 ^ (k + 1) * w = 2 * (2 ^ k * w) by ring]
    omega

theorem main_theorem_infinite (w : ℕ) (hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (r : ZMod p) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Reaches w n ∧ (n : ZMod p) = r := by
  have hp : p.Prime := Fact.out
  by_cases hp5 : 5 ≤ p
  · exact main_theorem_p_ge_5 p hp5 w hw hw3 r B
  · have hp23 : p = 2 ∨ p = 3 := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        intro h; rw [h] at hp; norm_num at hp
      omega
    rcases hp23 with rfl | rfl
    · exact main_theorem_p_eq_2 2 w hw hw3 rfl r B
    · exact main_theorem_p_eq_3 3 w hw hw3 rfl r B

theorem infinite_predecessors (w : ℕ) (hw : 0 < w) (hw3 : w % 3 ≠ 0) (r : ZMod p) :
    {n : ℕ | Reaches w n ∧ (n : ZMod p) = r}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, h1, h2⟩ := main_theorem_infinite p w hw hw3 r a
  exact ⟨n, ⟨h1, h2⟩, hn⟩

/-! ## The modular barrier on cycles -/

structure CycleSpec where
  k : ℕ
  S : ℕ
  N : ℕ

theorem reaching_predecessor_dense_mod_p {v : ℕ} (hv : 0 < v) (hv3 : v % 3 ≠ 0)
    (r : ZMod p) : ∃ n : ℕ, Reaches v n ∧ (n : ZMod p) = r := by
  obtain ⟨n, _, h1, h2⟩ := main_theorem_infinite p v hv hv3 r 0
  exact ⟨n, h1, h2⟩

theorem cycle_local_obstruction_barrier (spec : CycleSpec)
    (h_denom : ((2 ^ spec.S - 3 ^ spec.k : ℤ) : ZMod p) ≠ 0)
    {v : ℕ} (hv : 0 < v) (hv3 : v % 3 ≠ 0) :
    ∃ (n : ℕ), Reaches v n ∧
      ((2 ^ spec.S - 3 ^ spec.k : ℤ) : ZMod p) * (n : ZMod p) = (spec.N : ZMod p) := by
  obtain ⟨n, hn_reaches, hn_mod⟩ := reaching_predecessor_dense_mod_p p hv hv3
    (((2 ^ spec.S - 3 ^ spec.k : ℤ) : ZMod p)⁻¹ * (spec.N : ZMod p))
  refine ⟨n, hn_reaches, ?_⟩
  rw [hn_mod, ← mul_assoc, mul_inv_cancel₀ h_denom, one_mul]

end AtomicERE
