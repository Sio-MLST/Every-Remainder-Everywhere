import Mathlib

namespace ERE

variable (p : ℕ) [Fact p.Prime]

instance instNeZeroERE : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-! ## Domain and operators -/

def InG (x : ℕ) : Prop := 8 ≤ x ∧ (x % 9 = 2 ∨ x % 9 = 8)
def ValidClass (c : ℕ) : Prop := c % 9 = 2 ∨ c % 9 = 8
def R (x : ℕ) : ℕ := if x % 9 = 2 then 4 * x else 16 * x

def mult (x : ℕ) : ℕ :=
  if x % 27 = 2 then 4
  else if x % 27 = 8 then 8
  else if x % 27 = 11 then 16
  else if x % 27 = 17 then 2
  else if x % 27 = 20 then 4
  else 2

def L (x : ℕ) : ℕ := mult x * (2 * x - 1) / 6

inductive Desc (v : ℕ) : ℕ → Prop
  | refl : Desc v v
  | right {n : ℕ} : Desc v n → Desc v (R n)
  | left  {n : ℕ} : Desc v n → Desc v (L n)

theorem residue_mod27 {x : ℕ} (h : x % 9 = 2 ∨ x % 9 = 8) :
    x % 27 = 2 ∨ x % 27 = 8 ∨ x % 27 = 11 ∨
    x % 27 = 17 ∨ x % 27 = 20 ∨ x % 27 = 26 := by
  omega

theorem mult_mem (x : ℕ) :
    mult x = 2 ∨ mult x = 4 ∨ mult x = 8 ∨ mult x = 16 := by
  unfold mult
  split_ifs <;> omega

theorem mult_pow (x : ℕ) : ∃ k : ℕ, mult x = 2 ^ k := by
  rcases mult_mem x with h | h | h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨2, by simp [h]⟩
  · exact ⟨3, by simp [h]⟩
  · exact ⟨4, by simp [h]⟩

theorem L_spec {x : ℕ} (h : x % 3 = 2) :
    6 * L x = mult x * (2 * x - 1) := by
  have h2 : 2 ∣ mult x := by
    have := mult_mem x; omega
  have h3 : 3 ∣ 2 * x - 1 := by omega
  have h6 : 6 ∣ mult x * (2 * x - 1) := by
    obtain ⟨a, ha⟩ := h2
    obtain ⟨b, hb⟩ := h3
    exact ⟨a * b, by rw [ha, hb]; ring⟩
  unfold L
  exact Nat.mul_div_cancel' h6

theorem R_mem {x : ℕ} (h : InG x) : InG (R x) := by
  obtain ⟨h8, h9⟩ := h
  unfold InG R
  split_ifs with hx
  · exact ⟨by omega, Or.inr (by omega)⟩
  · exact ⟨by omega, Or.inl (by omega)⟩

theorem L_mem {x : ℕ} (h : InG x) : InG (L x) := by
  obtain ⟨h8, h9⟩ := h
  have hx3 : x % 3 = 2 := by omega
  have hs := L_spec hx3
  have h27 := residue_mod27 h9
  unfold InG
  unfold mult at hs
  split_ifs at hs <;> omega

theorem L_valid {x : ℕ} (h : x % 9 = 2 ∨ x % 9 = 8) : ValidClass (L x) := by
  have hx3 : x % 3 = 2 := by omega
  have hs := L_spec hx3
  have h27 := residue_mod27 h
  unfold ValidClass
  unfold mult at hs
  split_ifs at hs <;> omega

theorem Desc_mem {v n : ℕ} (hv : InG v) (h : Desc v n) : InG n := by
  induction h with
  | refl => exact hv
  | right _ ih => exact R_mem ih
  | left  _ ih => exact L_mem ih

/-! ## Precision loss under the left branch -/

theorem mod27_eq_of_mod_pow {K x y : ℕ} (hK : 1 ≤ K)
    (hxy : x % 3 ^ (K + 2) = y % 3 ^ (K + 2)) :
    x % 27 = y % 27 := by
  have hle : 3 ≤ K + 2 := by omega
  exact Nat.ModEq.of_dvd (pow_dvd_pow 3 hle) hxy

theorem mult_congr {x y : ℕ} (h : x % 27 = y % 27) :
    mult x = mult y := by
  unfold mult
  rw [h]

theorem L_cong {K x y : ℕ} (hK : 1 ≤ K)
    (hx : x % 3 = 2) (hy : y % 3 = 2)
    (hxy : x % 3 ^ (K + 2) = y % 3 ^ (K + 2)) :
    mult x = mult y ∧ L x % 3 ^ (K + 1) = L y % 3 ^ (K + 1) := by
  have h27 : x % 27 = y % 27 := mod27_eq_of_mod_pow hK hxy
  have hmult : mult x = mult y := mult_congr h27
  refine ⟨hmult, ?_⟩
  have hcast : ∀ z : ℕ, z % 3 = 2 →
      (6 : ℤ) * ((L z : ℕ) : ℤ) = ((mult z : ℕ) : ℤ) * (2 * (z : ℤ) - 1) := by
    intro z hz
    have h := congr_arg (fun n : ℕ => (n : ℤ)) (L_spec hz)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    rwa [Nat.cast_sub (by omega : 1 ≤ 2 * z)] at h
  have hLx := hcast x hx
  have hLy := hcast y hy
  rw [← hmult] at hLy
  have hxy' : x ≡ y [MOD 3 ^ (K + 2)] := hxy
  obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.1 hxy'
  have key : L x ≡ L y [MOD 3 ^ (K + 1)] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨((mult x : ℕ) : ℤ) * q, ?_⟩
    push_cast at hq ⊢
    apply mul_left_cancel₀ (show (6 : ℤ) ≠ 0 by norm_num)
    linear_combination hLy - hLx + 2 * ((mult x : ℕ) : ℤ) * hq
  exact key

/-! ## The right-branch cycle on residue classes -/

def rnext (K c : ℕ) : ℕ := R c % 3 ^ (K + 1)
def lnext (K e : ℕ) : ℕ := L e % 3 ^ (K + 1)

def rStep (c : ℕ) : ℕ := if c % 9 = 2 then 1 else 2

def rIter (K : ℕ) : ℕ → ℕ → ℕ
  | 0,     c => c
  | n + 1, c => rIter K n (rnext K c)

def rExp (K : ℕ) : ℕ → ℕ → ℕ
  | 0,     _ => 0
  | n + 1, c => rStep c + rExp K n (rnext K c)

theorem nine_dvd_pow {K : ℕ} (hK : 1 ≤ K) : 9 ∣ 3 ^ (K + 1) := by
  have h : (3 : ℕ) ^ 2 ∣ 3 ^ (K + 1) := pow_dvd_pow 3 (by omega)
  simpa using h

theorem validClass_mod {K : ℕ} (hK : 1 ≤ K) {e : ℕ} (he : ValidClass e) :
    ValidClass (e % 3 ^ (K + 1)) := by
  unfold ValidClass at *
  rw [Nat.mod_mod_of_dvd e (nine_dvd_pow hK)]
  exact he

theorem valid8 : ValidClass 8 := by
  unfold ValidClass; omega

theorem eight_lt {K : ℕ} (hK : 1 ≤ K) : 8 < 3 ^ (K + 1) := by
  have h9 : 9 ≤ 3 ^ (K + 1) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem rnext_valid {K : ℕ} (hK : 1 ≤ K) {c : ℕ} (hc : ValidClass c) :
    ValidClass (rnext K c) ∧ rnext K c < 3 ^ (K + 1) := by
  have h9 := nine_dvd_pow hK
  have hpos : 0 < 3 ^ (K + 1) := by positivity
  have hc' : c % 9 = 2 ∨ c % 9 = 8 := hc
  refine ⟨?_, Nat.mod_lt _ hpos⟩
  unfold ValidClass rnext
  rw [Nat.mod_mod_of_dvd _ h9]
  unfold R
  split_ifs with h <;> omega

theorem rIter_valid {K : ℕ} (hK : 1 ≤ K) {c : ℕ}
    (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) (n : ℕ) :
    ValidClass (rIter K n c) ∧ rIter K n c < 3 ^ (K + 1) := by
  induction n generalizing c with
  | zero => exact ⟨hc, hlt⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := rnext_valid hK hc
    exact ih h1 h2

theorem rIter_eq {K : ℕ} (hK : 1 ≤ K) {c : ℕ}
    (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) (n : ℕ) :
    rIter K n c % 3 ^ (K + 1) = (c * 4 ^ (rExp K n c)) % 3 ^ (K + 1) := by
  induction n generalizing c with
  | zero => simp [rIter, rExp]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := rnext_valid hK hc
    have ih' := ih h1 h2
    have hR : R c = c * 4 ^ rStep c := by
      unfold R rStep
      split_ifs <;> ring
    show rIter K n (rnext K c) % 3 ^ (K + 1)
      = c * 4 ^ (rStep c + rExp K n (rnext K c)) % 3 ^ (K + 1)
    rw [ih']
    have hm : (R c % 3 ^ (K + 1)) * 4 ^ rExp K n (rnext K c)
        ≡ R c * 4 ^ rExp K n (rnext K c) [MOD 3 ^ (K + 1)] :=
      (Nat.mod_modEq _ _).mul_right _
    have e : R c * 4 ^ rExp K n (rnext K c)
        = c * 4 ^ (rStep c + rExp K n (rnext K c)) := by
      rw [hR, pow_add]; ring
    change (R c % 3 ^ (K + 1)) * 4 ^ rExp K n (rnext K c) % 3 ^ (K + 1)
      = c * 4 ^ (rStep c + rExp K n (rnext K c)) % 3 ^ (K + 1)
    rw [← e]
    exact hm

theorem rIter_eq' {K : ℕ} (hK : 1 ≤ K) {c : ℕ}
    (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) (n : ℕ) :
    rIter K n c = (c * 4 ^ (rExp K n c)) % 3 ^ (K + 1) := by
  have h := rIter_eq hK hc hlt n
  have hv := (rIter_valid hK hc hlt n).2
  rw [Nat.mod_eq_of_lt hv] at h
  exact h

theorem rStep_pair {K : ℕ} (hK : 1 ≤ K) {c : ℕ} (hc : ValidClass c) :
    rStep c + rStep (rnext K c) = 3 := by
  have hc' : c % 9 = 2 ∨ c % 9 = 8 := hc
  unfold rStep rnext R
  rw [Nat.mod_mod_of_dvd _ (nine_dvd_pow hK)]
  split_ifs <;> omega

theorem rExp_two_mul {K : ℕ} (hK : 1 ≤ K) (k : ℕ) {c : ℕ}
    (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) :
    rExp K (2 * k) c = 3 * k := by
  induction k generalizing c with
  | zero => simp [rExp]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    have h1 := rnext_valid hK hc
    have h2 := rnext_valid hK h1.1
    show rStep c + (rStep (rnext K c) + rExp K (2 * k) (rnext K (rnext K c)))
      = 3 * (k + 1)
    rw [ih h2.1 h2.2]
    have := rStep_pair hK hc
    omega

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

theorem four_cancel {K a b : ℕ} (hab : a ≤ b)
    (h : 4 ^ a ≡ 4 ^ b [MOD 3 ^ (K + 1)]) : a ≡ b [MOD 3 ^ K] := by
  have hcop : Nat.gcd (3 ^ (K + 1)) (4 ^ a) = 1 :=
    Nat.Coprime.pow (K + 1) a (by norm_num)
  have hb : 4 ^ b = 4 ^ a * 4 ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  rw [hb] at h
  have h' : 4 ^ a * 1 ≡ 4 ^ a * 4 ^ (b - a) [MOD 3 ^ (K + 1)] := by
    rwa [mul_one]
  have h'' := Nat.ModEq.cancel_left_of_coprime hcop h'
  have h1 : 4 ^ (b - a) ≡ 1 [MOD 3 ^ (K + 1)] := h''.symm
  exact (Nat.modEq_iff_dvd' hab).2 ((four_pow_modEq_one_iff).1 h1)

theorem four_pow_mod9 (E : ℕ) :
    (E % 3 = 0 → 4 ^ E % 9 = 1) ∧ (E % 3 = 1 → 4 ^ E % 9 = 4)
    ∧ (E % 3 = 2 → 4 ^ E % 9 = 7) := by
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rcases Nat.lt_or_ge E 3 with h | h
    · interval_cases E <;> simp
    · obtain ⟨E', rfl⟩ : ∃ E', E = E' + 3 := ⟨E - 3, by omega⟩
      have h64 : 4 ^ (E' + 3) = 64 * 4 ^ E' := by ring
      obtain ⟨a, b, c⟩ := ih E' (by omega)
      rw [h64]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := a (by omega); omega
      · have := b (by omega); omega
      · have := c (by omega); omega

/-! ## Exponents and order -/

theorem rIter_modEq {K n c d : ℕ} (hK : 1 ≤ K) (hc : ValidClass c)
    (hcl : c < 3 ^ (K + 1)) (hd : d < 3 ^ (K + 1)) (h : rIter K n c = d) :
    c * 4 ^ rExp K n c ≡ d [MOD 3 ^ (K + 1)] := by
  have e := rIter_eq' hK hc hcl n
  rw [h] at e
  unfold Nat.ModEq
  rw [Nat.mod_eq_of_lt hd]
  exact e.symm

theorem exp_dvd_of_congr {b K E c c' : ℕ} (hb : b ≤ K) (hc : ¬ 3 ∣ c)
    (h : c * 4 ^ E ≡ c' [MOD 3 ^ (K + 1)]) (h' : c' ≡ c [MOD 3 ^ (b + 1)]) :
    3 ^ b ∣ E := by
  have hM : 3 ^ (b + 1) ∣ 3 ^ (K + 1) := pow_dvd_pow 3 (by omega)
  have h1 : c * 4 ^ E ≡ c' [MOD 3 ^ (b + 1)] := Nat.ModEq.of_dvd hM h
  have h2 : c * 4 ^ E ≡ c * 1 [MOD 3 ^ (b + 1)] := by
    rw [mul_one]; exact h1.trans h'
  have hcop : Nat.gcd (3 ^ (b + 1)) c = 1 :=
    Nat.Coprime.pow_left (b + 1) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hc)
  exact (four_pow_modEq_one_iff).1 (Nat.ModEq.cancel_left_of_coprime hcop h2)

theorem congr_of_exp_dvd {b K E c c' : ℕ} (hb : b ≤ K)
    (h : c * 4 ^ E ≡ c' [MOD 3 ^ (K + 1)]) (hE : 3 ^ b ∣ E) :
    c' ≡ c [MOD 3 ^ (b + 1)] := by
  have hM : 3 ^ (b + 1) ∣ 3 ^ (K + 1) := pow_dvd_pow 3 (by omega)
  have h1 : c * 4 ^ E ≡ c' [MOD 3 ^ (b + 1)] := Nat.ModEq.of_dvd hM h
  have h4 : 4 ^ E ≡ 1 [MOD 3 ^ (b + 1)] := (four_pow_modEq_one_iff).2 hE
  have h5 : c * 4 ^ E ≡ c * 1 [MOD 3 ^ (b + 1)] := h4.mul_left c
  rw [mul_one] at h5
  exact h1.symm.trans h5

theorem rExp_mod3 {K n c d : ℕ} (hK : 1 ≤ K) (hc : c % 9 = 2) (hd : d % 9 = 2)
    (hcl : c < 3 ^ (K + 1)) (h : rIter K n c = d) :
    rExp K n c % 3 = 0 := by
  have e1 := rIter_eq' hK (Or.inl hc : ValidClass c) hcl n
  rw [h] at e1
  have e2 : d % 9 = (c * 4 ^ rExp K n c) % 9 := by
    rw [e1]; exact Nat.mod_mod_of_dvd _ (nine_dvd_pow hK)
  have e3 := Nat.mul_mod c (4 ^ rExp K n c) 9
  rw [hc] at e3
  obtain ⟨a1, a2, a3⟩ := four_pow_mod9 (rExp K n c)
  have hcases : rExp K n c % 3 = 0 ∨ rExp K n c % 3 = 1 ∨ rExp K n c % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact h0
  · have := a2 h1; omega
  · have := a3 h2; omega

theorem four_pow_eq_one_of_mod3 {E : ℕ} (hE : E % 3 = 0)
    (h : (4 : ZMod p) ^ 3 = 1) : (4 : ZMod p) ^ E = 1 := by
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hE
  rw [hq, pow_mul, h, one_pow]

theorem exp_type {K : ℕ} (hK : 1 ≤ K) {c E : ℕ} (hc : ValidClass c)
    (h : c = 2 * 4 ^ E % 3 ^ (K + 1)) :
    (c % 9 = 2 ∧ E % 3 = 0) ∨ (c % 9 = 8 ∧ E % 3 = 1) := by
  have hc' : c % 9 = 2 ∨ c % 9 = 8 := hc
  have h9 : c % 9 = 2 * 4 ^ E % 9 := by
    rw [h]; exact Nat.mod_mod_of_dvd _ (nine_dvd_pow hK)
  obtain ⟨a, b, d⟩ := four_pow_mod9 E
  omega

/-! ## Existence of exponents via pigeonhole -/

theorem exists_exp {K : ℕ} (hK : 1 ≤ K) {c : ℕ}
    (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) :
    ∃ E : ℕ, c = 2 * 4 ^ E % 3 ^ (K + 1) := by
  classical
  have hc' : c % 9 = 2 ∨ c % 9 = 8 := hc
  have hcop : Nat.gcd (3 ^ (K + 1)) 2 = 1 := Nat.Coprime.pow_left (K + 1) (by decide)
  have hmap : ∀ E ∈ Finset.range (3 ^ K), 2 * 4 ^ E % 3 ^ (K + 1) ∈
      (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 = 2) := by
    intro E _
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega)), Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hinj : ∀ E1 E2, E1 ∈ Finset.range (3 ^ K) → E2 ∈ Finset.range (3 ^ K) →
      2 * 4 ^ E1 % 3 ^ (K + 1) = 2 * 4 ^ E2 % 3 ^ (K + 1) → E1 = E2 := by
    intro E1 E2 h1 h2 h
    rw [Finset.mem_range] at h1 h2
    have h4 : 4 ^ E1 ≡ 4 ^ E2 [MOD 3 ^ (K + 1)] :=
      Nat.ModEq.cancel_left_of_coprime hcop h
    rcases le_total E1 E2 with hle | hle
    · have he := four_cancel hle h4
      unfold Nat.ModEq at he
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at he
    · have he := four_cancel hle h4.symm
      unfold Nat.ModEq at he
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at he
      exact he.symm
  have hcard : ((Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 = 2)).card
      ≤ (Finset.range (3 ^ K)).card := by
    have hsub : (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 = 2)
        ⊆ (Finset.range (3 ^ K)).image (fun j => 3 * j + 2) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_range] at hw
      rw [Finset.mem_image]
      exact ⟨w / 3, Finset.mem_range.2 (by omega), by omega⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hcm : c ∈ (Finset.range (3 ^ (K + 1))).filter (fun w => w % 3 = 2) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, by omega⟩
  obtain ⟨E, _, hwE⟩ := Finset.surj_on_of_inj_on_of_card_le
    (fun E _ => 2 * 4 ^ E % 3 ^ (K + 1)) hmap hinj hcard c hcm
  exact ⟨E, hwE⟩

theorem R_transitive {K : ℕ} (hK : 1 ≤ K) {c d : ℕ}
    (hc : ValidClass c) (hcl : c < 3 ^ (K + 1))
    (hd : ValidClass d) (hdl : d < 3 ^ (K + 1)) :
    ∃ n, rIter K n c = d := by
  obtain ⟨Ec, hEc⟩ := exists_exp hK hc hcl
  obtain ⟨Ed, hEd⟩ := exists_exp hK hd hdl
  have tc := exp_type hK hc hEc
  have td := exp_type hK hd hEd
  have hq : 3 ∣ 3 ^ K * Ec := Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  obtain ⟨q, hq⟩ := hq
  have hle : Ec ≤ 3 ^ K * Ec := Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨y, hy⟩ : ∃ y, y + Ec = Ed + 3 * q := ⟨Ed + 3 * q - Ec, by omega⟩
  have hn : ∃ n, rExp K n c = y := by
    have hy3 : y % 3 = 0 ∨ y % 3 = 1 ∨ y % 3 = 2 := by omega
    have hv := rnext_valid hK hc
    rcases hy3 with h0 | h1 | h2
    · exact ⟨2 * (y / 3), by rw [rExp_two_mul hK _ hc hcl]; omega⟩
    all_goals
      refine ⟨2 * (y / 3) + 1, ?_⟩
      show rStep c + rExp K (2 * (y / 3)) (rnext K c) = y
      rw [rExp_two_mul hK _ hv.1 hv.2]
      unfold rStep
      split_ifs <;> omega
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [rIter_eq' hK hc hcl n, hn]
  have h1 : c * 4 ^ y ≡ 2 * 4 ^ Ec * 4 ^ y [MOD 3 ^ (K + 1)] := by
    rw [hEc]
    exact (Nat.mod_modEq _ _).mul_right _
  have hsum : Ec + y = Ed + 3 ^ K * Ec := by rw [hq]; omega
  have h2 : 2 * 4 ^ Ec * 4 ^ y = 2 * 4 ^ Ed * (4 ^ (3 ^ K)) ^ Ec := by
    calc 2 * 4 ^ Ec * 4 ^ y = 2 * 4 ^ (Ec + y) := by rw [pow_add]; ring
      _ = 2 * 4 ^ (Ed + 3 ^ K * Ec) := by rw [hsum]
      _ = 2 * 4 ^ Ed * (4 ^ (3 ^ K)) ^ Ec := by rw [pow_add, pow_mul]; ring
  have h3 : 4 ^ (3 ^ K) ≡ 1 [MOD 3 ^ (K + 1)] :=
    (four_pow_modEq_one_iff).2 dvd_rfl
  have h3' := h3.pow Ec
  rw [one_pow] at h3'
  have h4 : 2 * 4 ^ Ed * (4 ^ (3 ^ K)) ^ Ec ≡ 2 * 4 ^ Ed * 1 [MOD 3 ^ (K + 1)] :=
    h3'.mul_left _
  rw [h2] at h1
  rw [mul_one] at h4
  have h5 := h1.trans h4
  rw [hEd]
  exact h5

theorem R_full_loop {K : ℕ} (hK : 1 ≤ K) :
    ∃ n, 0 < n ∧ rIter K n 8 = 8 ∧ rExp K n 8 = 3 ^ K := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
  have h8 := eight_lt hK
  have hexp : rExp (j + 1) (2 * 3 ^ j) 8 = 3 ^ (j + 1) := by
    rw [rExp_two_mul hK _ valid8 h8]; ring
  refine ⟨2 * 3 ^ j, by positivity, ?_, hexp⟩
  rw [rIter_eq' hK valid8 h8, hexp]
  have h1 : 4 ^ (3 ^ (j + 1)) ≡ 1 [MOD 3 ^ (j + 1 + 1)] :=
    (four_pow_modEq_one_iff).2 dvd_rfl
  have h2 : 8 * 4 ^ (3 ^ (j + 1)) ≡ 8 * 1 [MOD 3 ^ (j + 1 + 1)] := h1.mul_left 8
  rw [mul_one] at h2
  have h3 : (8 * 4 ^ (3 ^ (j + 1))) % 3 ^ (j + 1 + 1) = 8 % 3 ^ (j + 1 + 1) := h2
  rw [h3]
  exact Nat.mod_eq_of_lt h8

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

def rightLabel (c : ℕ) : Aff p :=
  (if c % 9 = 2 then (4 : ZMod p) else 16, 0)

def leftLabel (e : ℕ) : Aff p :=
  ((mult e : ZMod p) / 3, -((mult e : ZMod p) / 6))

theorem rightLabel_fst (c : ℕ) : (rightLabel p c).1 = (4 : ZMod p) ^ rStep c := by
  unfold rightLabel rStep
  split_ifs <;> norm_num

theorem rightLabel_snd (c : ℕ) : (rightLabel p c).2 = 0 := by
  unfold rightLabel; rfl

inductive Edge (K : ℕ) : ℕ → ℕ → Aff p → Prop
  | right {c : ℕ} (hc : ValidClass c) (hlt : c < 3 ^ (K + 1)) :
      Edge K c (rnext K c) (rightLabel p c)
  | left  {e : ℕ} (he : ValidClass e) (hlt : e < 3 ^ (K + 2)) :
      Edge K (e % 3 ^ (K + 1)) (lnext K e) (leftLabel p e)

inductive Walk (K : ℕ) : ℕ → ℕ → Aff p → Prop
  | nil (c : ℕ) : Walk K c c (1, 0)
  | fwd {u w d : ℕ} {f g : Aff p} :
      Edge p K u w f → Walk K w d g → Walk K u d (athen p f g)
  | bwd {u w d : ℕ} {f g : Aff p} :
      Edge p K u w f → Walk K u d g → Walk K w d (athen p (ainv p f) g)

def Hol (K : ℕ) : Set (Aff p) := {f | Walk p K 8 8 f}

def HasTranslation (K : ℕ) : Prop :=
  ∃ d : ZMod p, d ≠ 0 ∧ ((1 : ZMod p), d) ∈ Hol p K

theorem Walk.append {K u w d : ℕ} {f g : Aff p}
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

theorem four_ne_zero_zmod (hp5 : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have h : (4 : ZMod p) = 2 ^ 2 := by norm_num
  rw [h]; exact pow_ne_zero 2 (two_ne_zero_zmod p hp5)

theorem six_ne_zero_zmod (hp5 : 5 ≤ p) : (6 : ZMod p) ≠ 0 := by
  have h : (6 : ZMod p) = 2 * 3 := by norm_num
  rw [h]; exact mul_ne_zero (two_ne_zero_zmod p hp5) (three_ne_zero_zmod p hp5)

theorem mult_cast_ne_zero (hp5 : 5 ≤ p) (x : ℕ) :
    (mult x : ZMod p) ≠ 0 := by
  obtain ⟨k, hk⟩ := mult_pow x
  rw [hk]
  push_cast
  exact pow_ne_zero k (two_ne_zero_zmod p hp5)

theorem Edge.label_unit (hp5 : 5 ≤ p) {K u w : ℕ} {f : Aff p}
    (h : Edge p K u w f) : f.1 ≠ 0 := by
  have h2 := two_ne_zero_zmod p hp5
  have h3 := three_ne_zero_zmod p hp5
  cases h with
  | right hc hlt =>
    rw [rightLabel_fst]
    exact pow_ne_zero _ (four_ne_zero_zmod p hp5)
  | left he hlt =>
    simp only [leftLabel]
    exact div_ne_zero (mult_cast_ne_zero p hp5 _) h3

theorem Walk.label_unit (hp5 : 5 ≤ p) {K u w : ℕ} {f : Aff p}
    (h : Walk p K u w f) : f.1 ≠ 0 := by
  induction h with
  | nil c => simp
  | fwd he hw ih =>
    simp only [athen]
    exact mul_ne_zero ih (Edge.label_unit p hp5 he)
  | bwd he hw ih =>
    simp only [athen, ainv]
    exact mul_ne_zero ih (inv_ne_zero (Edge.label_unit p hp5 he))

theorem Walk.symm (hp5 : 5 ≤ p) {K u w : ℕ} {f : Aff p}
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
    (hf : f ∈ Hol p K) (hg : g ∈ Hol p K) :
    athen p f g ∈ Hol p K := Walk.append p hf hg

theorem Hol_inv (hp5 : 5 ≤ p) {K : ℕ} {f : Aff p}
    (hf : f ∈ Hol p K) : ainv p f ∈ Hol p K := Walk.symm p hp5 hf

theorem walk_of_rIter {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    ∀ {c : ℕ}, ValidClass c → c < 3 ^ (K + 1) →
      ∃ g : Aff p, Walk p K c (rIter K n c) g
        ∧ g = ((4 : ZMod p) ^ rExp K n c, 0) := by
  induction n with
  | zero =>
    intro c hc hlt
    exact ⟨(1, 0), Walk.nil c, by simp [rExp]⟩
  | succ n ih =>
    intro c hc hlt
    obtain ⟨h1, h2⟩ := rnext_valid hK hc
    obtain ⟨g, hg, rfl⟩ := ih h1 h2
    refine ⟨athen p (rightLabel p c) _, Walk.fwd (Edge.right hc hlt) hg, ?_⟩
    show athen p (rightLabel p c) ((4 : ZMod p) ^ rExp K n (rnext K c), 0)
      = ((4 : ZMod p) ^ (rStep c + rExp K n (rnext K c)), 0)
    unfold athen
    rw [rightLabel_fst, rightLabel_snd]
    ext <;> simp [pow_add, mul_comm]

/-! ## Fibres -/

def M (K v : ℕ) : Set (ℕ × ZMod p) :=
  {q | ∃ n, Desc v n ∧ q = (n % 3 ^ (K + 1), (n : ZMod p))}

def fibre (K v c : ℕ) : Set (ZMod p) := {t | (c, t) ∈ M p K v}

theorem R_class {K : ℕ} (hK : 1 ≤ K) {x : ℕ} (_h : InG x) :
    R x % 3 ^ (K + 1) = rnext K (x % 3 ^ (K + 1)) := by
  have hm : x % 3 ^ (K + 1) % 9 = x % 9 := Nat.mod_mod_of_dvd x (nine_dvd_pow hK)
  unfold rnext R
  rw [hm]
  split_ifs
  · exact (Nat.mul_mod_mod _ _ _).symm
  · exact (Nat.mul_mod_mod _ _ _).symm

theorem L_class {K : ℕ} (hK : 1 ≤ K) {x : ℕ} (h : InG x) :
    L x % 3 ^ (K + 1) = lnext K (x % 3 ^ (K + 2)) := by
  obtain ⟨h8, h9⟩ := h
  have hx3 : x % 3 = 2 := by omega
  have h3 : 3 ∣ 3 ^ (K + 2) := dvd_pow_self 3 (by omega)
  have hy3 : x % 3 ^ (K + 2) % 3 = 2 := by
    rw [Nat.mod_mod_of_dvd x h3]; exact hx3
  unfold lnext
  exact (L_cong hK hx3 hy3 (Nat.mod_mod _ _).symm).2

theorem R_label {x : ℕ} (_h : InG x) :
    ((R x : ℕ) : ZMod p) = aapp p (rightLabel p x) (x : ZMod p) := by
  unfold R rightLabel aapp
  split_ifs <;> simp

theorem L_label (hp5 : 5 ≤ p) {x : ℕ} (h : InG x) :
    ((L x : ℕ) : ZMod p) = aapp p (leftLabel p x) (x : ZMod p) := by
  obtain ⟨h8, h9⟩ := h
  have hx3 : x % 3 = 2 := by omega
  have hs := L_spec hx3
  have hpos : 1 ≤ 2 * x := by omega
  have hc : (6 : ZMod p) * (L x : ZMod p)
      = (mult x : ZMod p) * (2 * (x : ZMod p) - 1) := by
    have h' := congr_arg (Nat.cast : ℕ → ZMod p) hs
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hpos] at h'
    push_cast at h'
    exact h'
  have h6 := six_ne_zero_zmod p hp5
  have h3 := three_ne_zero_zmod p hp5
  have e : (6 : ZMod p) * aapp p (leftLabel p x) (x : ZMod p)
      = (mult x : ZMod p) * (2 * (x : ZMod p) - 1) := by
    simp only [aapp, leftLabel]
    field_simp
    ring
  exact mul_left_cancel₀ h6 (hc.trans e.symm)

theorem rightLabel_mod {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    rightLabel p (n % 3 ^ (K + 1)) = rightLabel p n := by
  unfold rightLabel
  rw [Nat.mod_mod_of_dvd n (nine_dvd_pow hK)]

theorem leftLabel_mod {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    leftLabel p (n % 3 ^ (K + 2)) = leftLabel p n := by
  have h27 : 27 ∣ 3 ^ (K + 2) := by
    have h : (3 : ℕ) ^ 3 ∣ 3 ^ (K + 2) := pow_dvd_pow 3 (by omega)
    simpa using h
  have : mult (n % 3 ^ (K + 2)) = mult n :=
    mult_congr (Nat.mod_mod_of_dvd n h27)
  unfold leftLabel
  rw [this]

theorem fibre_right {K v c : ℕ} (hK : 1 ≤ K) (hv : InG v) {t : ZMod p}
    (ht : t ∈ fibre p K v c) :
    aapp p (rightLabel p c) t ∈ fibre p K v (rnext K c) := by
  obtain ⟨n, hn, hq⟩ := ht
  have h1 : c = n % 3 ^ (K + 1) := (Prod.mk.inj hq).1
  have h2 : t = (n : ZMod p) := (Prod.mk.inj hq).2
  have hnG := Desc_mem hv hn
  refine ⟨R n, Desc.right hn, ?_⟩
  subst h1
  subst h2
  rw [R_class hK hnG, R_label p hnG, rightLabel_mod p hK n]

theorem fibre_left (hp5 : 5 ≤ p) {K v e : ℕ} (hK : 1 ≤ K) (hv : InG v)
    {t : ZMod p} (ht : t ∈ fibre p (K + 1) v e) :
    aapp p (leftLabel p e) t ∈ fibre p K v (lnext K e) := by
  obtain ⟨n, hn, hq⟩ := ht
  have h1 : e = n % 3 ^ (K + 2) := (Prod.mk.inj hq).1
  have h2 : t = (n : ZMod p) := (Prod.mk.inj hq).2
  have hnG := Desc_mem hv hn
  refine ⟨L n, Desc.left hn, ?_⟩
  subst h1
  subst h2
  rw [L_class hK hnG, L_label p hp5 hnG, leftLabel_mod p hK n]

theorem fibre_proj {J K v c : ℕ} (hJK : J ≤ K) {t : ZMod p}
    (ht : t ∈ fibre p K v c) :
    t ∈ fibre p J v (c % 3 ^ (J + 1)) := by
  obtain ⟨n, hn, hq⟩ := ht
  refine ⟨n, hn, ?_⟩
  have h1 : n % 3 ^ (K + 1) = c := (Prod.mk.inj hq).1.symm
  have h2 : t = (n : ZMod p) := (Prod.mk.inj hq).2
  rw [← h1, Nat.mod_mod_of_dvd _ (pow_dvd_pow 3 (by omega))]
  simp [h2]

theorem fibre_root_nonempty (K v : ℕ) :
    (fibre p K v (v % 3 ^ (K + 1))).Nonempty :=
  ⟨(v : ZMod p), v, Desc.refl, rfl⟩

/-! ## Stabilisation of fibre cardinalities -/

theorem fibre_ncard_step (hp5 : 5 ≤ p) {v : ℕ} (hv : InG v) {K : ℕ}
    (hK : 1 ≤ K) (c : ℕ) :
    (fibre p K v c).ncard ≤ (fibre p K v (rnext K c)).ncard := by
  have hs : (rightLabel p c).1 ≠ 0 := by
    rw [rightLabel_fst]; exact pow_ne_zero _ (four_ne_zero_zmod p hp5)
  have hinj := aapp_inj p (rightLabel p c) hs
  have himg : (aapp p (rightLabel p c)) '' (fibre p K v c) ⊆ fibre p K v (rnext K c) := by
    rintro _ ⟨t, ht, rfl⟩
    exact fibre_right p hK hv ht
  calc (fibre p K v c).ncard
      = ((aapp p (rightLabel p c)) '' (fibre p K v c)).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ (fibre p K v (rnext K c)).ncard := Set.ncard_le_ncard himg

theorem fibre_ncard_chain (hp5 : 5 ≤ p) {v : ℕ} (hv : InG v) {K : ℕ}
    (hK : 1 ≤ K) (n : ℕ) :
    ∀ {c : ℕ}, ValidClass c → c < 3 ^ (K + 1) →
      (fibre p K v c).ncard ≤ (fibre p K v (rIter K n c)).ncard := by
  induction n with
  | zero => intro c hc hlt; exact le_refl _
  | succ n ih =>
    intro c hc hlt
    have hv' := rnext_valid hK hc
    exact (fibre_ncard_step p hp5 hv hK c).trans (ih hv'.1 hv'.2)

theorem fibre_ncard_const (hp5 : 5 ≤ p) {v : ℕ} (hv : InG v) {K : ℕ}
    (hK : 1 ≤ K) {c d : ℕ}
    (hc : ValidClass c) (hcl : c < 3 ^ (K + 1))
    (hd : ValidClass d) (hdl : d < 3 ^ (K + 1)) :
    (fibre p K v c).ncard = (fibre p K v d).ncard := by
  obtain ⟨n, hn⟩ := R_transitive hK hc hcl hd hdl
  obtain ⟨m, hm⟩ := R_transitive hK hd hdl hc hcl
  have h1 := fibre_ncard_chain p hp5 hv hK n hc hcl
  have h2 := fibre_ncard_chain p hp5 hv hK m hd hdl
  rw [hn] at h1
  rw [hm] at h2
  exact le_antisymm h1 h2

theorem fibre_ncard_antitone {v : ℕ} (K : ℕ) (hK : 1 ≤ K) :
    (fibre p (K + 1) v 8).ncard ≤ (fibre p K v 8).ncard := by
  have h8 := eight_lt hK
  have hsub : fibre p (K + 1) v 8 ⊆ fibre p K v 8 := by
    intro t ht
    have := fibre_proj p (Nat.le_succ K) ht
    rwa [Nat.mod_eq_of_lt h8] at this
  exact Set.ncard_le_ncard hsub

theorem stabilization (hp5 : 5 ≤ p) {v : ℕ} (hv : InG v) :
    ∃ K0 σ : ℕ, 1 ≤ K0 ∧ 1 ≤ σ ∧
      ∀ K, K0 ≤ K → ∀ c, ValidClass c → c < 3 ^ (K + 1) →
        (fibre p K v c).ncard = σ := by
  classical
  have hv9 : ValidClass v := by
    obtain ⟨_, h⟩ := hv
    exact h
  have hpos : ∀ K, 1 ≤ K → 1 ≤ (fibre p K v 8).ncard := by
    intro K hK
    have hvc : ValidClass (v % 3 ^ (K + 1)) := validClass_mod hK hv9
    have hvl : v % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
    have heq := fibre_ncard_const p hp5 hv hK hvc hvl valid8 (eight_lt hK)
    have hne := fibre_root_nonempty p K v
    have : 0 < (fibre p K v (v % 3 ^ (K + 1))).ncard :=
      (Set.ncard_pos (Set.toFinite _)).2 hne
    omega
  have hex : ∃ m, ∃ K, 1 ≤ K ∧ (fibre p K v 8).ncard = m := ⟨_, 1, le_refl _, rfl⟩
  obtain ⟨K0, hK0, hm⟩ := Nat.find_spec hex
  have hmin : ∀ K, 1 ≤ K → Nat.find hex ≤ (fibre p K v 8).ncard :=
    fun K hK => Nat.find_min' hex ⟨K, hK, rfl⟩
  have hdown : ∀ K, K0 ≤ K → (fibre p K v 8).ncard ≤ (fibre p K0 v 8).ncard := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => exact le_refl _
    | succ K hK ih => exact (fibre_ncard_antitone p K (by omega)).trans ih
  have hconst : ∀ K, K0 ≤ K → (fibre p K v 8).ncard = Nat.find hex := by
    intro K hK
    have h1 := hdown K hK
    have h2 := hmin K (by omega)
    omega
  refine ⟨K0, Nat.find hex, hK0, ?_, ?_⟩
  · have := hpos K0 hK0
    omega
  · intro K hK c hc hcl
    have h1 := fibre_ncard_const p hp5 hv (by omega) hc hcl valid8 (eight_lt (by omega))
    rw [h1]
    exact hconst K hK

theorem fibre_succ_eq (_hp5 : 5 ≤ p) {v K0 σ : ℕ} (_hv : InG v)
    (hσ : ∀ K, K0 ≤ K → ∀ c, ValidClass c → c < 3 ^ (K + 1) →
            (fibre p K v c).ncard = σ)
    {K : ℕ} (hK : K0 ≤ K) (hK1 : 1 ≤ K) {e : ℕ}
    (he : ValidClass e) (hel : e < 3 ^ (K + 2)) :
    fibre p (K + 1) v e = fibre p K v (e % 3 ^ (K + 1)) := by
  have hsub : fibre p (K + 1) v e ⊆ fibre p K v (e % 3 ^ (K + 1)) :=
    fun t ht => fibre_proj p (Nat.le_succ K) ht
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  have h1 := hσ (K + 1) (by omega) e he hel
  have h2 := hσ K hK (e % 3 ^ (K + 1)) (validClass_mod hK1 he)
    (Nat.mod_lt _ (by positivity))
  omega

theorem edge_image (hp5 : 5 ≤ p) {v K0 σ : ℕ} (hv : InG v)
    (hσ : ∀ K, K0 ≤ K → ∀ c, ValidClass c → c < 3 ^ (K + 1) →
            (fibre p K v c).ncard = σ)
    {K : ℕ} (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : ℕ} {f : Aff p}
    (h : Edge p K u w f) :
    (aapp p f) '' (fibre p K v u) = fibre p K v w := by
  have hf := Edge.label_unit p hp5 h
  have hinj := aapp_inj p f hf
  cases h with
  | right hc hlt =>
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact fibre_right p hK1 hv ht
    · have hv' := rnext_valid hK1 hc
      apply le_of_eq
      rw [Set.ncard_image_of_injective _ hinj, hσ K hK _ hc hlt,
        hσ K hK _ hv'.1 hv'.2]
  | @left e he hlt =>
    have hsucc := fibre_succ_eq p hp5 hv hσ hK hK1 he hlt
    have hl : ValidClass (lnext K e) := validClass_mod hK1 (L_valid he)
    have hll : lnext K e < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      rw [← hsucc] at ht
      exact fibre_left p hp5 hK1 hv ht
    · apply le_of_eq
      rw [Set.ncard_image_of_injective _ hinj,
        hσ K hK _ (validClass_mod hK1 he) (Nat.mod_lt _ (by positivity)),
        hσ K hK _ hl hll]

theorem walk_image (hp5 : 5 ≤ p) {v K0 σ : ℕ} (hv : InG v)
    (hσ : ∀ K, K0 ≤ K → ∀ c, ValidClass c → c < 3 ^ (K + 1) →
            (fibre p K v c).ncard = σ)
    {K : ℕ} (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : ℕ} {f : Aff p}
    (h : Walk p K u w f) :
    (aapp p f) '' (fibre p K v u) = fibre p K v w := by
  induction h with
  | nil c =>
    ext t
    simp [aapp]
  | @fwd u w d f g he hw ih =>
    have e1 := edge_image p hp5 hv hσ hK hK1 he
    have hfun : aapp p (athen p f g) = aapp p g ∘ aapp p f :=
      funext (athen_app p f g)
    rw [hfun, Set.image_comp, e1, ih]
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have e1 := edge_image p hp5 hv hσ hK hK1 he
    have e2 : (aapp p (ainv p f)) '' (fibre p K v w) = fibre p K v u := by
      rw [← e1, ← Set.image_comp]
      have : aapp p (ainv p f) ∘ aapp p f = id := funext (ainv_app p f hf)
      rw [this, Set.image_id]
    have hfun : aapp p (athen p (ainv p f) g) = aapp p g ∘ aapp p (ainv p f) :=
      funext (athen_app p (ainv p f) g)
    rw [hfun, Set.image_comp, e2, ih]

/-! ## Commutator identity -/

theorem comm_label (lam α β : ZMod p) (hl : lam ≠ 0) (ha : α ≠ 0) :
    athen p (athen p (athen p (ainv p (α, β)) (ainv p (lam, 0))) (α, β)) (lam, 0)
      = (1, (lam - 1) * β) := by
  ext
  · simp [athen, ainv]; try field_simp
  · simp [athen, ainv]; try field_simp; try ring

theorem translation_of_dilation (hp5 : 5 ≤ p) {K : ℕ}
    {lam α β : ZMod p}
    (hl0 : lam ≠ 0) (hl1 : lam ≠ 1) (ha : α ≠ 0) (hb : β ≠ 0)
    (hμ : (lam, (0 : ZMod p)) ∈ Hol p K)
    (hh : (α, β) ∈ Hol p K) :
    HasTranslation p K := by
  have h := Hol_mul p
    (Hol_mul p (Hol_mul p (Hol_inv p hp5 hh) (Hol_inv p hp5 hμ)) hh) hμ
  rw [comm_label p lam α β hl0 ha] at h
  exact ⟨(lam - 1) * β, mul_ne_zero (sub_ne_zero.2 hl1) hb, h⟩

/-! ## Existence of a nontrivial translation -/

theorem ref_walk (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    ∃ α β : ZMod p, α ≠ 0 ∧ β ≠ 0 ∧ (α, β) ∈ Hol p K := by
  have h8 := eight_lt hK
  have e8 : 8 % 3 ^ (K + 1) = 8 := Nat.mod_eq_of_lt h8
  have hv1 : ValidClass (lnext K 8) :=
    validClass_mod hK (L_valid (x := 8) (Or.inr (by norm_num)))
  have hl1 : lnext K 8 < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  obtain ⟨n, hn⟩ := R_transitive hK hv1 hl1 valid8 h8
  obtain ⟨g, hg, hgeq⟩ := walk_of_rIter p hK n hv1 hl1
  rw [hn] at hg
  have hl : Edge p K (8 % 3 ^ (K + 1)) (lnext K 8) (leftLabel p 8) :=
    Edge.left valid8
      (lt_of_lt_of_le h8 (Nat.pow_le_pow_right (by norm_num) (by omega)))
  rw [e8] at hl
  have hw := Walk.fwd hl hg
  have h4 := four_ne_zero_zmod p hp5
  have h6 := six_ne_zero_zmod p hp5
  refine ⟨(athen p (leftLabel p 8) g).1, (athen p (leftLabel p 8) g).2,
    Walk.label_unit p hp5 hw, ?_, hw⟩
  rw [hgeq]
  show (4 : ZMod p) ^ rExp K n (lnext K 8) * (-((mult 8 : ZMod p) / 6)) + 0 ≠ 0
  rw [add_zero]
  exact mul_ne_zero (pow_ne_zero _ h4)
    (neg_ne_zero.2 (div_ne_zero (mult_cast_ne_zero p hp5 8) h6))

theorem dil_case1 (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K)
    (h : (4 : ZMod p) ^ (3 ^ K) ≠ 1) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ lam ≠ 1 ∧
      (lam, (0 : ZMod p)) ∈ Hol p K := by
  obtain ⟨n, hn0, hloop, hexp⟩ := R_full_loop hK
  obtain ⟨g, hg, hgeq⟩ := walk_of_rIter p hK n valid8 (eight_lt hK)
  rw [hloop] at hg
  rw [hexp] at hgeq
  refine ⟨(4 : ZMod p) ^ (3 ^ K), pow_ne_zero _ (four_ne_zero_zmod p hp5), h, ?_⟩
  rw [hgeq] at hg
  exact hg

theorem rpath {K : ℕ} (hK : 1 ≤ K) {c d : ℕ}
    (hc : ValidClass c) (hcl : c < 3 ^ (K + 1))
    (hd : ValidClass d) (hdl : d < 3 ^ (K + 1)) :
    ∃ n : ℕ, rIter K n c = d ∧
      Walk p K c d ((4 : ZMod p) ^ rExp K n c, 0) := by
  obtain ⟨n, hn⟩ := R_transitive hK hc hcl hd hdl
  obtain ⟨g, hg, rfl⟩ := walk_of_rIter p hK n hc hcl
  rw [hn] at hg
  exact ⟨n, hn, hg⟩

theorem pure_dilation_of_pair (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) {e1 e2 : ℕ}
    (he1 : ValidClass e1) (hl1 : e1 < 3 ^ (K + 2))
    (he2 : ValidClass e2) (hl2 : e2 < 3 ^ (K + 2))
    {ns nt : ℕ}
    (hs : rIter K ns (e1 % 3 ^ (K + 1)) = e2 % 3 ^ (K + 1))
    (hs1 : (4 : ZMod p) ^ rExp K ns (e1 % 3 ^ (K + 1)) = 1)
    (ht : rIter K nt (lnext K e1) = lnext K e2) :
    (((mult e2 : ℕ) : ZMod p) /
        (((mult e1 : ℕ) : ZMod p) * (4 : ZMod p) ^ rExp K nt (lnext K e1)),
      (0 : ZMod p)) ∈ Hol p K := by
  have hu1 := validClass_mod hK he1
  have hu1l : e1 % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hw1 : ValidClass (lnext K e1) := validClass_mod hK (L_valid he1)
  have hw1l : lnext K e1 < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have h8 := eight_lt hK
  obtain ⟨g, hgW, rfl⟩ := walk_of_rIter p hK ns hu1 hu1l
  rw [hs, hs1] at hgW
  obtain ⟨g', hgW', rfl⟩ := walk_of_rIter p hK nt hw1 hw1l
  rw [ht] at hgW'
  obtain ⟨n0, hn0, hγ⟩ := rpath p hK valid8 h8 hw1 hw1l
  have E1 : Edge p K (e1 % 3 ^ (K + 1)) (lnext K e1) (leftLabel p e1) :=
    Edge.left he1 hl1
  have E2 : Edge p K (e2 % 3 ^ (K + 1)) (lnext K e2) (leftLabel p e2) :=
    Edge.left he2 hl2
  have W1 : Walk p K (lnext K e1) (e1 % 3 ^ (K + 1))
      (athen p (ainv p (leftLabel p e1)) (1, 0)) := Walk.bwd E1 (Walk.nil _)
  have W2 : Walk p K (e2 % 3 ^ (K + 1)) (lnext K e2)
      (athen p (leftLabel p e2) (1, 0)) := Walk.fwd E2 (Walk.nil _)
  have Wt := Walk.symm p hp5 hgW'
  have Ω := Walk.append p (Walk.append p (Walk.append p W1 hgW) W2) Wt
  have hfull := Walk.append p (Walk.append p hγ Ω) (Walk.symm p hp5 hγ)
  have hm1 : ((mult e1 : ℕ) : ZMod p) ≠ 0 := mult_cast_ne_zero p hp5 e1
  have hm2 : ((mult e2 : ℕ) : ZMod p) ≠ 0 := mult_cast_ne_zero p hp5 e2
  have h4 := four_ne_zero_zmod p hp5
  have h3 := three_ne_zero_zmod p hp5
  have h6 := six_ne_zero_zmod p hp5
  have ha : (4 : ZMod p) ^ rExp K n0 8 ≠ 0 := pow_ne_zero _ h4
  have hτ : (4 : ZMod p) ^ rExp K nt (lnext K e1) ≠ 0 := pow_ne_zero _ h4
  show Walk p K 8 8 _
  convert hfull using 1
  apply Prod.ext
  · simp only [athen, ainv, leftLabel]; field_simp
  · simp only [athen, ainv, leftLabel]; field_simp; try ring

theorem dil_case2a (hp5 : 5 ≤ p) {K a : ℕ}
    (hK : 1 ≤ K) (ha2 : 2 ≤ a) (haK : a ≤ K)
    (hord : orderOf (4 : ZMod p) = 3 ^ a) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ lam ≠ 1 ∧
      (lam, (0 : ZMod p)) ∈ Hol p K := by
  obtain ⟨j, rfl⟩ : ∃ j, a = j + 2 := ⟨a - 2, by omega⟩
  have hQ : 0 < 3 ^ j := by positivity
  have hA : 3 ^ (j + 2 + 1) = 27 * 3 ^ j := by ring
  have hdN : 3 ^ (j + 2 + 1) ∣ 3 ^ (K + 1) := pow_dvd_pow 3 (by omega)
  have hN : 3 ^ (j + 2 + 1) ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hN2 : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := by ring
  have h8 := eight_lt hK
  have he2 : ValidClass (8 + 27 * 3 ^ j) := by unfold ValidClass; omega
  have hl1 : 8 < 3 ^ (K + 2) := by omega
  have hl2 : 8 + 27 * 3 ^ j < 3 ^ (K + 2) := by omega
  have hmult1 : mult 8 = 8 := by decide
  have hmult2 : mult (8 + 27 * 3 ^ j) = 8 := by
    unfold mult
    have h27e : (8 + 27 * 3 ^ j) % 27 = 8 := by omega
    simp [h27e]
  have hL1 : L 8 = 20 := by decide
  have hL2 : L (8 + 27 * 3 ^ j) = 20 + 72 * 3 ^ j := by
    have hs := L_spec (x := 8 + 27 * 3 ^ j) (by omega)
    rw [hmult2] at hs
    omega
  have hu1 := validClass_mod hK valid8
  have hu1l : 8 % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hu2 := validClass_mod hK he2
  have hu2l : (8 + 27 * 3 ^ j) % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hw1 : ValidClass (lnext K 8) :=
    validClass_mod hK (L_valid (x := 8) (Or.inr (by norm_num)))
  have hw1l : lnext K 8 < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hw2 : ValidClass (lnext K (8 + 27 * 3 ^ j)) :=
    validClass_mod hK (L_valid (x := 8 + 27 * 3 ^ j) (Or.inr (by omega)))
  have hw2l : lnext K (8 + 27 * 3 ^ j) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  obtain ⟨ns, hs⟩ := R_transitive hK hu1 hu1l hu2 hu2l
  have hs1 : (4 : ZMod p) ^ rExp K ns (8 % 3 ^ (K + 1)) = 1 := by
    have hmod := rIter_modEq hK hu1 hu1l hu2l hs
    have hdv : 3 ^ (j + 2) ∣ rExp K ns (8 % 3 ^ (K + 1)) := by
      refine exp_dvd_of_congr (b := j + 2) (by omega) ?_ hmod ?_
      · rw [Nat.mod_eq_of_lt h8]; omega
      · have a1 : (8 + 27 * 3 ^ j) % 3 ^ (K + 1) ≡ 8 + 27 * 3 ^ j [MOD 3 ^ (j + 2 + 1)] :=
          Nat.ModEq.of_dvd hdN (Nat.mod_modEq _ _)
        have a2 : 8 + 27 * 3 ^ j ≡ 8 [MOD 3 ^ (j + 2 + 1)] := by
          show (8 + 27 * 3 ^ j) % 3 ^ (j + 2 + 1) = 8 % 3 ^ (j + 2 + 1)
          rw [hA]; exact Nat.add_mod_right _ _
        have a3 : 8 % 3 ^ (K + 1) ≡ 8 [MOD 3 ^ (j + 2 + 1)] :=
          Nat.ModEq.of_dvd hdN (Nat.mod_modEq _ _)
        exact (a1.trans a2).trans a3.symm
    exact (orderOf_dvd_iff_pow_eq_one).1 (by rw [hord]; exact hdv)
  obtain ⟨nt, ht⟩ := R_transitive hK hw1 hw1l hw2 hw2l
  have hτ : (4 : ZMod p) ^ rExp K nt (lnext K 8) ≠ 1 := by
    intro h1
    have hdv : 3 ^ (j + 2) ∣ rExp K nt (lnext K 8) := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one h1
    have hmod := rIter_modEq hK hw1 hw1l hw2l ht
    have hc := congr_of_exp_dvd (b := j + 2) (by omega) hmod hdv
    unfold lnext at hc
    rw [hL2, hL1] at hc
    have b1 : 20 + 72 * 3 ^ j ≡ 20 [MOD 3 ^ (j + 2 + 1)] :=
      ((Nat.ModEq.of_dvd hdN (Nat.mod_modEq (20 + 72 * 3 ^ j) _)).symm.trans hc).trans
        (Nat.ModEq.of_dvd hdN (Nat.mod_modEq 20 _))
    have hd := (Nat.modEq_iff_dvd' (by omega)).1 b1.symm
    rw [hA, Nat.add_sub_cancel_left] at hd
    have := Nat.dvd_of_mul_dvd_mul_right hQ hd
    omega
  have hpair := pure_dilation_of_pair p hp5 hK valid8 hl1 he2 hl2 hs hs1 ht
  have hm0 := mult_cast_ne_zero p hp5 8
  have hτ0 : (4 : ZMod p) ^ rExp K nt (lnext K 8) ≠ 0 :=
    pow_ne_zero _ (four_ne_zero_zmod p hp5)
  refine ⟨_, div_ne_zero (mult_cast_ne_zero p hp5 _) (mul_ne_zero hm0 hτ0), ?_, hpair⟩
  intro h
  rw [hmult2] at h
  have hm8 : ((8 : ℕ) : ZMod p) ≠ 0 := by rw [← hmult1]; exact hm0
  rw [div_eq_one_iff_eq (mul_ne_zero (by rw [hmult1]; exact hm0) hτ0)] at h
  rw [hmult1] at h
  exact hτ (mul_left_cancel₀ hm8 (by rw [mul_one]; exact h.symm))

theorem dil_case2b (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K)
    (hord : orderOf (4 : ZMod p) = 3) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ lam ≠ 1 ∧
      (lam, (0 : ZMod p)) ∈ Hol p K := by
  have h43 : (4 : ZMod p) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (4 : ZMod p)
    rwa [hord] at this
  have h27 : (3 : ℕ) ^ 3 ≤ 3 ^ (K + 2) :=
    Nat.pow_le_pow_right (by norm_num) (show 3 ≤ K + 2 by omega)
  have h27' : 27 ≤ 3 ^ (K + 2) := by simpa using h27
  have h9 := nine_dvd_pow hK
  have hL2 : L 2 = 2 := by decide
  have hL11 : L 11 = 56 := by decide
  have hm2 : mult 2 = 4 := by decide
  have hm11 : mult 11 = 16 := by decide
  have he1 : ValidClass 2 := by unfold ValidClass; omega
  have he2 : ValidClass 11 := by unfold ValidClass; omega
  have hl1 : 2 < 3 ^ (K + 2) := by omega
  have hl2 : 11 < 3 ^ (K + 2) := by omega
  have hu1 := validClass_mod hK he1
  have hu1l : 2 % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hu2 := validClass_mod hK he2
  have hu2l : 11 % 3 ^ (K + 1) < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hw1 : ValidClass (lnext K 2) :=
    validClass_mod hK (L_valid (x := 2) (Or.inl (by norm_num)))
  have hw1l : lnext K 2 < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have hw2 : ValidClass (lnext K 11) :=
    validClass_mod hK (L_valid (x := 11) (Or.inl (by norm_num)))
  have hw2l : lnext K 11 < 3 ^ (K + 1) := Nat.mod_lt _ (by positivity)
  have m1 : (2 % 3 ^ (K + 1)) % 9 = 2 := by
    rw [Nat.mod_mod_of_dvd _ h9]
  have m2 : (11 % 3 ^ (K + 1)) % 9 = 2 := by
    rw [Nat.mod_mod_of_dvd _ h9]
  have m3 : lnext K 2 % 9 = 2 := by
    show L 2 % 3 ^ (K + 1) % 9 = 2
    rw [Nat.mod_mod_of_dvd _ h9, hL2]
  have m4 : lnext K 11 % 9 = 2 := by
    show L 11 % 3 ^ (K + 1) % 9 = 2
    rw [Nat.mod_mod_of_dvd _ h9, hL11]
  obtain ⟨ns, hs⟩ := R_transitive hK hu1 hu1l hu2 hu2l
  obtain ⟨nt, ht⟩ := R_transitive hK hw1 hw1l hw2 hw2l
  have hs1 := four_pow_eq_one_of_mod3 p (rExp_mod3 hK m1 m2 hu1l hs) h43
  have ht1 := four_pow_eq_one_of_mod3 p (rExp_mod3 hK m3 m4 hw1l ht) h43
  have hpair := pure_dilation_of_pair p hp5 hK he1 hl1 he2 hl2 hs hs1 ht
  have hτ0 : (4 : ZMod p) ^ rExp K nt (lnext K 2) ≠ 0 :=
    pow_ne_zero _ (four_ne_zero_zmod p hp5)
  have hm20 := mult_cast_ne_zero p hp5 2
  refine ⟨_, div_ne_zero (mult_cast_ne_zero p hp5 _) (mul_ne_zero hm20 hτ0), ?_, hpair⟩
  intro h
  rw [ht1, hm11, hm2] at h
  push_cast at h
  have h4 := four_ne_zero_zmod p hp5
  rw [div_eq_one_iff_eq (by simpa using h4)] at h
  have h12 : (3 : ZMod p) * 4 = 0 := by linear_combination h
  rcases mul_eq_zero.1 h12 with h3 | h4'
  · exact three_ne_zero_zmod p hp5 h3
  · exact h4 h4'

theorem order_split (hp5 : 5 ≤ p) {K : ℕ}
    (h : (4 : ZMod p) ^ (3 ^ K) = 1) :
    ∃ a, 1 ≤ a ∧ a ≤ K ∧ orderOf (4 : ZMod p) = 3 ^ a := by
  have hdvd : orderOf (4 : ZMod p) ∣ 3 ^ K :=
    orderOf_dvd_of_pow_eq_one h
  obtain ⟨a, haK, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  refine ⟨a, ?_, haK, ha⟩
  by_contra ha0
  have ha0' : a = 0 := by omega
  rw [ha0', pow_zero, orderOf_eq_one_iff] at ha
  have h3 : ((3 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination ha
  have hdvd3 : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp h3
  have := Nat.le_of_dvd (by norm_num) hdvd3
  omega

theorem dilation_exists (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    ∃ lam : ZMod p, lam ≠ 0 ∧ lam ≠ 1 ∧
      (lam, (0 : ZMod p)) ∈ Hol p K := by
  by_cases h : (4 : ZMod p) ^ (3 ^ K) = 1
  · obtain ⟨a, ha1, haK, hord⟩ := order_split p hp5 h
    by_cases ha : a = 1
    · subst ha
      exact dil_case2b p hp5 hK (by simpa using hord)
    · exact dil_case2a p hp5 hK (by omega) haK hord
  · exact dil_case1 p hp5 hK h

theorem translation_exists (hp5 : 5 ≤ p) {K : ℕ} (hK : 1 ≤ K) :
    HasTranslation p K := by
  obtain ⟨lam, hl0, hl1, hμ⟩ := dilation_exists p hp5 hK
  obtain ⟨α, β, ha, hb, hh⟩ := ref_walk p hp5 hK
  exact translation_of_dilation p hp5 hl0 hl1 ha hb hμ hh

/-! ## Simultaneous density -/

theorem main_theorem_core (hp5 : 5 ≤ p) {v : ℕ} (hv : InG v)
    {J : ℕ} (hJ : 1 ≤ J) {c : ℕ}
    (hc : ValidClass c) (hcl : c < 3 ^ (J + 1)) (r : ZMod p) :
    ∃ y, Desc v y ∧ y % 3 ^ (J + 1) = c ∧ (y : ZMod p) = r := by
  obtain ⟨K0, σ, hK0, hσ1, hσ⟩ := stabilization p hp5 hv
  set K := max (max K0 J) 1 with hKdef
  have hKK0 : K0 ≤ K := by omega
  have hKJ  : J  ≤ K := by omega
  have hK1  : 1  ≤ K := by omega
  have h9 : 9 ≤ 3 ^ (K + 1) :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : 8 < 3 ^ (K + 1) := by omega
  have h8v : ValidClass 8 := Or.inr (by norm_num [ValidClass])

  obtain ⟨d, hd0, hd⟩ := translation_exists p hp5 hK1
  have himg := walk_image p hp5 hv hσ hKK0 hK1 hd
  obtain ⟨t0, ht0⟩ : (fibre p K v 8).Nonempty := by
    have : (fibre p K v 8).ncard = σ := hσ K hKK0 8 h8v h8
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  have step : ∀ t ∈ fibre p K v 8, t + d ∈ fibre p K v 8 := by
    intro t ht
    have h1 : aapp p (1, d) t ∈ (aapp p (1, d)) '' fibre p K v 8 :=
      ⟨t, ht, rfl⟩
    rw [himg] at h1
    simpa [aapp] using h1
  have key : ∀ k : ℕ, t0 + (k : ZMod p) * d ∈ fibre p K v 8 := by
    intro k
    induction k with
    | zero => simpa using ht0
    | succ k ih =>
      have := step _ ih
      convert this using 1
      push_cast; ring

  have hfull8 : fibre p K v 8 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro r'
    have := key ((r' - t0) / d).val
    rw [ZMod.natCast_zmod_val] at this
    have e : t0 + (r' - t0) / d * d = r' := by field_simp; ring
    rwa [e] at this
  have hσp : σ = p := by
    have h := hσ K hKK0 8 h8v h8
    rw [hfull8, Set.ncard_univ, Nat.card_zmod] at h
    exact h.symm
  have huniv : (Set.univ : Set (ZMod p)).ncard = p := by
    rw [Set.ncard_univ, Nat.card_zmod]
  have hcK : c < 3 ^ (K + 1) :=
    lt_of_lt_of_le hcl (Nat.pow_le_pow_right (by norm_num) (by omega))

  have hfullc : fibre p K v c = Set.univ := by
    have hc' := hσ K hKK0 c hc hcK
    exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by omega)
  have hr : r ∈ fibre p K v c := by rw [hfullc]; trivial
  have hr' := fibre_proj p hKJ hr
  have hcmod : c % 3 ^ (J + 1) = c := Nat.mod_eq_of_lt hcl
  rw [hcmod] at hr'
  obtain ⟨n, hn, hpair⟩ := hr'
  exact ⟨n, hn, (Prod.mk.inj hpair).1.symm, (Prod.mk.inj hpair).2.symm⟩

/-! ## Collatz layer: descendants reach their seed -/

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

theorem R_reaches (x : ℕ) : ∃ j, collatz^[j] (R x) = x := by
  unfold R
  split_ifs
  · exact ⟨2, by rw [show (4 : ℕ) * x = 2 ^ 2 * x by norm_num]; exact collatz_pow_mul 2 x⟩
  · exact ⟨4, by rw [show (16 : ℕ) * x = 2 ^ 4 * x by norm_num]; exact collatz_pow_mul 4 x⟩

theorem L_reaches {x : ℕ} (hx1 : 1 ≤ x) (hx3 : x % 3 = 2) :
    ∃ j, collatz^[j] (L x) = x := by
  have hs := L_spec hx3
  obtain ⟨i, hmi⟩ : ∃ i, mult x = 2 * 2 ^ i := by
    rcases mult_mem x with h | h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
    · exact ⟨3, by simp [h]⟩
  obtain ⟨m, hm⟩ : ∃ m, 2 * x - 1 = 3 * m := ⟨(2 * x - 1) / 3, by omega⟩
  have hL : L x = 2 ^ i * m := by
    have h6 : 6 * L x = 6 * (2 ^ i * m) := by
      rw [hs, hmi, hm]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h6
  have e1 : collatz m = 2 * x := by
    unfold collatz
    split_ifs with h <;> omega
  refine ⟨2 + i, ?_⟩
  rw [Function.iterate_add_apply, hL, collatz_pow_mul]
  show collatz (collatz m) = x
  rw [e1, collatz_double]

theorem Desc_reaches {v n : ℕ} (hv : InG v) (h : Desc v n) : Reaches v n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @right n hn ih =>
    obtain ⟨j, hj⟩ := R_reaches n
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + j, by rw [Function.iterate_add_apply, hj, hk]⟩
  | @left n hn ih =>
    have hI : InG n := Desc_mem hv hn
    have h8 : 8 ≤ n := hI.1
    have h9 : n % 9 = 2 ∨ n % 9 = 8 := hI.2
    have hn3 : n % 3 = 2 := by omega
    have hn1 : 1 ≤ n := by omega
    obtain ⟨j, hj⟩ := L_reaches hn1 hn3
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + j, by rw [Function.iterate_add_apply, hj, hk]⟩

theorem collatz_8 : collatz^[3] 8 = 1 := by decide

theorem inverse_tree_covers (r : ZMod p) :
    ∃ n : ℕ, 0 < n ∧ Reaches 1 n ∧ (n : ZMod p) = r := by
  have hp : p.Prime := Fact.out
  have h2 := hp.two_le
  by_cases hp5 : 5 ≤ p
  · have hv8 : InG 8 := by unfold InG; omega
    obtain ⟨y, hy, -, hyr⟩ :=
      main_theorem_core p hp5 hv8 (J := 1) le_rfl valid8 (by norm_num) r
    obtain ⟨k, hk⟩ := Desc_reaches hv8 hy
    have hI : InG y := Desc_mem hv8 hy
    have h8 : 8 ≤ y := hI.1
    exact ⟨y, by omega, ⟨3 + k, by rw [Function.iterate_add_apply, hk, collatz_8]⟩, hyr⟩
  · have hp23 : p = 2 ∨ p = 3 := by
      have h4 : p ≠ 4 := by
        intro h; rw [h] at hp; norm_num at hp
      omega
    have hlt := ZMod.val_lt r
    by_cases h0 : r.val = 0
    · refine ⟨p, hp.pos, ?_, ?_⟩
      · rcases hp23 with h | h <;> rw [h]
        · exact ⟨1, by decide⟩
        · exact ⟨7, by decide⟩
      · rw [ZMod.natCast_self]
        exact ((ZMod.val_eq_zero r).1 h0).symm
    · have hn : r.val = 1 ∨ r.val = 2 := by omega
      refine ⟨r.val, by omega, ?_, ZMod.natCast_zmod_val r⟩
      rcases hn with h | h <;> rw [h]
      · exact ⟨0, rfl⟩
      · exact ⟨1, by decide⟩

theorem reaches_trans {a b c : ℕ} (h1 : Reaches b a) (h2 : Reaches c b) : Reaches c a := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [Function.iterate_add_apply, hk1, hk2]⟩

theorem exists_inG_reaches (m : ℕ) (hm : 0 < m) (hm3 : m % 3 ≠ 0) :
    ∃ v, InG v ∧ Reaches m v := by
  have hm9 : m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 7 ∨ m % 9 = 8 := by omega
  rcases hm9 with h | h | h | h | h | h
  · refine ⟨128 * m, ⟨by omega, Or.inl (by omega)⟩, ⟨7, collatz_pow_mul 7 m⟩⟩
  · refine ⟨64 * m, ⟨by omega, Or.inl (by omega)⟩, ⟨6, collatz_pow_mul 6 m⟩⟩
  · refine ⟨128 * m, ⟨by omega, Or.inr (by omega)⟩, ⟨7, collatz_pow_mul 7 m⟩⟩
  · refine ⟨256 * m, ⟨by omega, Or.inl (by omega)⟩, ⟨8, collatz_pow_mul 8 m⟩⟩
  · refine ⟨512 * m, ⟨by omega, Or.inl (by omega)⟩, ⟨9, collatz_pow_mul 9 m⟩⟩
  · refine ⟨64 * m, ⟨by omega, Or.inr (by omega)⟩, ⟨6, collatz_pow_mul 6 m⟩⟩

/-! ## General targets and modular bridges -/

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

lemma ge_of_mod_eq {y c M : ℕ} (_hc : c < M) (hmod : y % M = c) (_hy : 0 < y) :
    c ≤ y := by
  rw [← hmod]
  exact Nat.mod_le y M

lemma exists_large_valid_class (B : ℕ) :
    ∃ J c : ℕ, 1 ≤ J ∧ ValidClass c ∧ c < 3 ^ (J + 1) ∧ B < c := by
  have hpos : 0 < 3 ^ B := by positivity
  refine ⟨B + 1, 9 * 3 ^ B - 1, by omega, ?_, ?_, ?_⟩
  · unfold ValidClass; omega
  · rw [show 3 ^ (B + 1 + 1) = 9 * 3 ^ B by ring]; omega
  · have hB : B < 3 ^ B := Nat.lt_pow_self (by norm_num)
    omega

lemma cast_eq_of_mod {p : ℕ} [Fact p.Prime] {n : ℕ} {r : ZMod p} (h : n % p = r.val) :
    (n : ZMod p) = r := by
  rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]

lemma cast_eq_of_mod' {p q : ℕ} [Fact p.Prime] (hpq : p = q) {n : ℕ} {r : ZMod p}
    (h : n % q = r.val) : (n : ZMod p) = r := by
  apply cast_eq_of_mod
  have : n % p = n % q := by rw [hpq]
  rw [this]; exact h

lemma four_pow_mod_three (j : ℕ) : 4 ^ j % 3 = 1 := by
  induction j with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma sixtyfour_pow_mod (t : ℕ) : 64 ^ t % 9 = 1 := by
  induction t with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

lemma lt_pow_mul {B k w : ℕ} (hk : B ≤ k) (hw : 0 < w) : B < 2 ^ k * w := by
  have h1 : k < 2 ^ k := Nat.lt_pow_self (by norm_num)
  have h2 : 2 ^ k ≤ 2 ^ k * w := Nat.le_mul_of_pos_right _ hw
  omega

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

/-! ## The three cases and the master theorem -/

theorem main_theorem_p_ge_5 (hp5 : 5 ≤ p)
    (w : ℕ) (hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (r : ZMod p) (B : ℕ) :
    ∃ n : ℕ, B < n ∧ Reaches w n ∧ (n : ZMod p) = r := by
  obtain ⟨v, hv, hvw⟩ := exists_inG_reaches w hw hw3
  obtain ⟨J, c, hJ, hc, hcl, hBc⟩ := exists_large_valid_class B
  obtain ⟨y, hy, hymod, hyr⟩ := main_theorem_core p hp5 hv hJ hc hcl r
  have hy0 : 0 < y := Nat.pos_of_ne_zero (by rintro rfl; simp at hymod; omega)
  have hcy := ge_of_mod_eq hcl hymod hy0
  exact ⟨y, by omega, reaches_trans (Desc_reaches hv hy) hvw, hyr⟩

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

/-! ## Modular solvability of cycle equations -/

theorem cycle_equation_solvable_mod_p (S k N : ℕ)
    (h : ((2 ^ S - 3 ^ k : ℤ) : ZMod p) ≠ 0) :
    ∃ r : ZMod p, ((2 ^ S - 3 ^ k : ℤ) : ZMod p) * r = (N : ZMod p) := by
  refine ⟨((2 ^ S - 3 ^ k : ℤ) : ZMod p)⁻¹ * (N : ZMod p), ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

/-! ## The modular barrier on cycles -/

structure CycleSpec where
  k : ℕ
  S : ℕ
  N : ℕ

theorem reaching_predecessor_dense_mod_p {v : ℕ} (hv : 0 < v) (hv3 : v % 3 ≠ 0)
    (r : ZMod p) :
    ∃ n : ℕ, Reaches v n ∧ (n : ZMod p) = r := by
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

end ERE
