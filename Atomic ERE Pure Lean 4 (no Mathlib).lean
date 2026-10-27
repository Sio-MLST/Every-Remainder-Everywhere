/-!
# Every Remainder Everywhere (atomic form), pure Lean 4: no Mathlib

Backward Collatz steps: `D n = 2n` and `U n = (n-1)/3` (allowed when `n % 6 = 4` and the result
is not a multiple of 3). Theorem (`main_theorem`, last part of this file):

  For every prime `p`, every `w > 0` with `3 ∤ w`, every residue `r` and every bound `B`
  there is `n > B` such that `n` reaches `w` under the Collatz map and `n ≡ r (mod p)`.

## How to check
* Toolchain: `leanprover/lean4:v4.36.0-rc1`. The file has no `import`: it uses only Lean core
  (`omega`, `grind`, the core `List`/`Nat`/`Fin` libraries). Run `lean AtomicERE_pure.lean`.
* Expected output: only the final `#print axioms` line
  (`propext`, `Classical.choice`, `Quot.sound`). No errors, no warnings, no `sorry`.

## What a reader must trust
Only the *statement*: the definitions `collatz`, `iter`, `Reaches`, `IsPrime` and the type of
`main_theorem`. Everything else is proved. (`Tree` and the other definitions are tools inside
the proof, not part of the statement.)

## Differences from a Mathlib-style development
* `ZMod p` is `Fin p`; the cast of a natural number is `cs p n`. Powers of 2 and 4 modulo `p`
  are stated on natural numbers (`cs p (4 ^ m) = 1`), never as powers in `Fin p`.
* Sets of residues are predicates `Fin p → Prop`; `card` counts them by a filtered list, and the
  pigeonhole principle is `List.Nodup.length_le_of_subset`.
* `padicValNat` is replaced by an elementary lifting-the-exponent lemma for the base 4.
* `orderOf` is replaced by the predicate `Q m := cs p (4 ^ m) = 1` (Part 8b).
* `Nat.find` is replaced by `stabilize_nat`, and `Finset` by lists.
* Primality is used in exactly one place: `isPrime_pfield` (every nonzero residue has an inverse).
  Everything else needs only `5 ≤ p` and that field property.

## Reading map
* Part 1. The Collatz layer, reachability and the atomic tree.
* Part 2. 3-adic arithmetic: lifting-the-exponent for the base 4, and the order of 2 modulo 3^(K+1).
* Part 3. Multiplication by 2 runs through all units modulo 3^(K+1) (a list-based pigeonhole argument).
* Part 4. Residues modulo p (`Fin p`), the field hypothesis `PField`, and counting subsets of `Fin p`.
* Part 5. Affine labels t ↦ s·t + b on `Fin p`.
* Part 6. Edges D and U, walks, and the holonomy group.
* Part 7a. Fibres and their cardinalities.
* Part 7b. Doubling and undo on fibres; sizes sigma_K.
* Part 7c. Stabilisation, and the action of edges and walks on stabilised fibres.
* Part 8a. Flat assignments: collapse, normalisation, Phi(2^j) = 2^j, powers of 4.
* Part 8b. The order of 4 modulo p, stated on exponents.
* Part 8c. No flat assignment exists (the arithmetic obstruction).
* Part 9a. Connectivity of the state graph; a common fixed point yields a flat assignment.
* Part 9b. No common fixed point implies a nonzero translation in the holonomy group.
* Part 9c. Simultaneous density modulo a prime, and primality implies the field property.
* Part 10. Small primes (2 and 3) and the master theorem.
-/

namespace AtomicERE

/-! ## Part 1. The Collatz layer, reachability and the atomic tree.
     (`collatz`, `iter`, `Reaches` and `Tree` are the definitions the main theorem talks about.) -/
def collatz (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter f k (f n)

theorem iter_add (f : Nat → Nat) (m n : Nat) : ∀ x, iter f (m + n) x = iter f m (iter f n x) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih => intro x; exact ih (f x)

def Reaches (v n : Nat) : Prop := ∃ k, iter collatz k n = v

theorem collatz_double (a : Nat) : collatz (2 * a) = a := by
  unfold collatz; split <;> omega

theorem collatz_pow_mul (j m : Nat) : iter collatz j (2 ^ j * m) = m := by
  induction j with
  | zero => simp [iter]
  | succ j ih =>
    rw [show 2 ^ (j + 1) * m = 2 * (2 ^ j * m) by rw [Nat.pow_succ]; grind]
    show iter collatz j (collatz (2 * (2 ^ j * m))) = m
    rw [collatz_double, ih]

theorem reaches_trans {a b c : Nat} (h1 : Reaches b a) (h2 : Reaches c b) : Reaches c a := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [iter_add, hk1, hk2]⟩

theorem collatz_eq_iff (m n : Nat) :
    collatz m = n ↔ m = 2 * n ∨ (m % 2 = 1 ∧ 3 * m + 1 = n) := by
  unfold collatz; split <;> omega

theorem pred_of_three_dvd {m n : Nat} (hn : n % 3 = 0) (h : collatz m = n) : m = 2 * n := by
  rcases (collatz_eq_iff m n).1 h with h1 | ⟨h2, h3⟩ <;> omega

theorem reaches_of_three_dvd {w : Nat} (hw : w % 3 = 0) {n : Nat} :
    Reaches w n ↔ ∃ k, n = 2 ^ k * w := by
  constructor
  · rintro ⟨k, hk⟩
    induction k generalizing n with
    | zero => exact ⟨0, by simpa [iter] using hk.symm.symm⟩
    | succ k ih =>
      have hk' : iter collatz k (collatz n) = w := hk
      obtain ⟨j, hj⟩ := ih hk'
      by_cases hev : n % 2 = 0
      · refine ⟨j + 1, ?_⟩
        have hc : collatz n = n / 2 := by unfold collatz; simp [hev]
        rw [hc] at hj
        have hp : 2 ^ (j + 1) * w = 2 * (2 ^ j * w) := by rw [Nat.pow_succ]; grind
        rw [hp]; omega
      · exfalso
        have hc : collatz n = 3 * n + 1 := by unfold collatz; simp [hev]
        rw [hc] at hj
        obtain ⟨a, ha⟩ : 3 ∣ w := Nat.dvd_of_mod_eq_zero hw
        have h3 : 2 ^ j * w = 3 * (2 ^ j * a) := by rw [ha]; grind
        omega
  · rintro ⟨k, rfl⟩
    exact ⟨k, collatz_pow_mul k w⟩

inductive Tree (v : Nat) : Nat → Prop
  | seed : Tree v v
  | D {n : Nat} : Tree v n → Tree v (2 * n)
  | U {n : Nat} : Tree v n → n % 6 = 4 → ((n - 1) / 3) % 3 ≠ 0 → Tree v ((n - 1) / 3)

theorem Tree_live {v n : Nat} (hv3 : v % 3 ≠ 0) (h : Tree v n) : n % 3 ≠ 0 := by
  induction h with
  | seed => exact hv3
  | D _ ih => omega
  | U _ _ h3 _ => exact h3

theorem Tree_reaches {v n : Nat} (h : Tree v n) : Reaches v n := by
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

/-! ## Part 2. 3-adic arithmetic: lifting-the-exponent for the base 4, and the order of 2 modulo 3^(K+1). -/
theorem three_dvd_pow (K : Nat) : 3 ∣ 3 ^ (K + 1) := ⟨3 ^ K, by rw [Nat.pow_succ, Nat.mul_comm]⟩

theorem one_lt_pow3 (K : Nat) : 1 < 3 ^ (K + 1) :=
  Nat.one_lt_pow (Nat.succ_ne_zero K) (by decide)

theorem mod_unit {M c : Nat} (h3 : 3 ∣ M) (hc : c % 3 ≠ 0) : c % M % 3 ≠ 0 := by
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

theorem pow_one_add {s : Nat} (_hs : 1 ≤ s) (w : Nat) :
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

theorem four_pow_modEq_one_iff {K m : Nat} : 4 ^ m % 3 ^ (K + 1) = 1 ↔ 3 ^ K ∣ m := by
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
        obtain ⟨z, hz⟩ := pow_one_add (s := K + 1) (by omega) w k
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

theorem two_pow_modEq_one_iff {K m : Nat} : 2 ^ m % 3 ^ (K + 1) = 1 ↔ 2 * 3 ^ K ∣ m := by
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
    exact Nat.mul_dvd_mul_left 2 (four_pow_modEq_one_iff.1 h)
  · rintro ⟨q, rfl⟩
    have h : 4 ^ (3 ^ K) % 3 ^ (K + 1) = 1 := four_pow_modEq_one_iff.2 (Nat.dvd_refl _)
    have e : 2 ^ (2 * 3 ^ K * q) = (4 ^ (3 ^ K)) ^ q := by
      rw [Nat.mul_assoc, Nat.pow_mul 2 2 (3 ^ K * q), ← Nat.pow_mul 4 (3 ^ K) q]
      try rfl
    rw [e, Nat.pow_mod, h, Nat.one_pow]
    exact Nat.mod_eq_of_lt (one_lt_pow3 K)

theorem cancel_left_pow {M a x y : Nat} (hcop : Nat.Coprime M a) (hxy : y ≤ x)
    (h : (a * x) % M = (a * y) % M) : x % M = y % M := by
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
  have h2 : a * x - a * y = a * (x - y) := (Nat.mul_sub a x y).symm
  rw [h2] at h1
  have h3 : M ∣ a * (x - y) := Nat.dvd_of_mod_eq_zero h1
  have h4 : M ∣ x - y := Nat.Coprime.dvd_of_dvd_mul_left hcop h3
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
    have h'' := cancel_left_pow hcop hpos h'
    have hd := two_pow_modEq_one_iff.1 (by rw [h'']; exact Nat.mod_eq_of_lt (one_lt_pow3 K))
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

theorem four_pow_cong {K : Nat} (hK : 1 ≤ K) :
    4 ^ (3 ^ (K - 1)) % 3 ^ (K + 1) = (1 + 3 ^ K) % 3 ^ (K + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨q, hq⟩ := four_pow_form n
  rw [hq]
  show (1 + 3 ^ (n + 1) + 3 ^ (n + 2) * q) % 3 ^ (n + 2) = (1 + 3 ^ (n + 1)) % 3 ^ (n + 2)
  exact Nat.add_mul_mod_self_left _ _ _

/-! ## Part 3. Multiplication by 2 runs through all units modulo 3^(K+1) (a list-based pigeonhole argument). -/
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

theorem cancel_right_pow {M c x y : Nat} (hcop : Nat.Coprime M c)
    (h : (x * c) % M = (y * c) % M) : x % M = y % M := by
  rcases Nat.le_total y x with hle | hle
  · exact cancel_left_pow hcop hle (by rwa [Nat.mul_comm c x, Nat.mul_comm c y])
  · exact (cancel_left_pow hcop hle (by rw [Nat.mul_comm c x, Nat.mul_comm c y]; exact h.symm)).symm

theorem two_transitive {K c d : Nat} (hc : c % 3 ≠ 0) (hd : d % 3 ≠ 0)
    (hdl : d < 3 ^ (K + 1)) : ∃ j, (2 ^ j * c) % 3 ^ (K + 1) = d := by
  apply Classical.byContradiction
  intro hno
  have hno' : ∀ j, (2 ^ j * c) % 3 ^ (K + 1) ≠ d := fun j hj => hno ⟨j, hj⟩
  have hM : 3 ^ (K + 1) = 3 * 3 ^ K := by rw [Nat.pow_succ]; grind
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
    have h1 := cancel_right_pow hcop heq
    exact hab (two_pow_inj ha hb h1)
  have hL1U : L1 ⊆ U := by
    intro w hw
    unfold L1 at hw
    rw [List.mem_map] at hw
    obtain ⟨E, _, rfl⟩ := hw
    unfold U
    rw [List.mem_filter, List.mem_range]
    refine ⟨Nat.mod_lt _ (by omega), ?_⟩
    have := mod_unit (three_dvd_pow K) (unit_mul (two_pow_mod_three_ne E) hc)
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

/-! ## Part 4. Residues modulo p (`Fin p`), the field hypothesis `PField`, and counting subsets of `Fin p`. -/
section Residues
variable (p : Nat) [NeZero p]

def cs (n : Nat) : Fin p := Fin.ofNat p n

theorem cs_val (n : Nat) : (cs p n).val = n % p := Fin.val_ofNat p n

theorem cs_eq_iff (a b : Nat) : cs p a = cs p b ↔ a % p = b % p := by
  constructor
  · intro h; have := congrArg Fin.val h; rwa [cs_val, cs_val] at this
  · intro h; apply Fin.ext; rw [cs_val, cs_val]; exact h

theorem cs_add (a b : Nat) : cs p (a + b) = cs p a + cs p b := by
  apply Fin.ext; rw [Fin.val_add, cs_val, cs_val, cs_val, Nat.add_mod]

theorem cs_mul (a b : Nat) : cs p (a * b) = cs p a * cs p b := by
  apply Fin.ext; rw [Fin.val_mul, cs_val, cs_val, cs_val, Nat.mul_mod]

theorem cs_zero : cs p 0 = (0 : Fin p) := rfl
theorem cs_one : cs p 1 = (1 : Fin p) := rfl
theorem cs_two : cs p 2 = (2 : Fin p) := rfl
theorem cs_three : cs p 3 = (3 : Fin p) := rfl
theorem cs_four : cs p 4 = (4 : Fin p) := rfl

theorem two_ne_zero_fin (hp5 : 5 ≤ p) : (2 : Fin p) ≠ 0 := by
  intro h
  have : cs p 2 = cs p 0 := h
  rw [cs_eq_iff, Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
  omega

theorem three_ne_zero_fin (hp5 : 5 ≤ p) : (3 : Fin p) ≠ 0 := by
  intro h
  have : cs p 3 = cs p 0 := h
  rw [cs_eq_iff, Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
  omega

/-- Every nonzero residue has an inverse: this holds exactly when `p` is prime. -/
class PField (p : Nat) [NeZero p] : Prop where
  inv_ex : ∀ a : Fin p, a ≠ 0 → ∃ b : Fin p, a * b = 1

open Classical in
noncomputable def finv (a : Fin p) : Fin p := if h : ∃ b : Fin p, a * b = 1 then h.choose else 0

theorem mul_finv {a : Fin p} (h : ∃ b : Fin p, a * b = 1) : a * finv p a = 1 := by
  unfold finv
  split
  · rename_i h'; exact h'.choose_spec
  · rename_i h'; exact absurd h h'

theorem mul_finv' [PField p] {a : Fin p} (h : a ≠ 0) : a * finv p a = 1 :=
  mul_finv p (PField.inv_ex a h)

theorem cancel_unit {u v a b : Fin p} (hu : u * v = 1) (h : u * a = u * b) : a = b := by
  calc a = (u * v) * a := by rw [hu]; grind
    _ = v * (u * a) := by grind
    _ = v * (u * b) := by rw [h]
    _ = (u * v) * b := by grind
    _ = b := by rw [hu]; grind

end Residues

/-! ## Counting subsets of `Fin p` -/

section Counting
variable {p : Nat}

open Classical in
noncomputable def card (S : Fin p → Prop) : Nat :=
  ((List.finRange p).filter (fun t => decide (S t))).length

open Classical in
theorem mem_cardlist {S : Fin p → Prop} {t : Fin p} :
    t ∈ (List.finRange p).filter (fun t => decide (S t)) ↔ S t := by
  rw [List.mem_filter]; simp [List.mem_finRange]

open Classical in
theorem card_le_of_inj {S T : Fin p → Prop} (g : Fin p → Fin p)
    (hinj : ∀ a b, g a = g b → a = b) (hmap : ∀ t, S t → T (g t)) : card S ≤ card T := by
  unfold card
  have hnd : ((List.finRange p).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange p)
  have hnd2 : (((List.finRange p).filter (fun t => decide (S t))).map g).Nodup := by
    apply List.pairwise_map.2
    apply List.Pairwise.imp_of_mem _ hnd
    intro a b _ _ hab hg
    exact hab (hinj a b hg)
  have hsub : ((List.finRange p).filter (fun t => decide (S t))).map g
      ⊆ (List.finRange p).filter (fun t => decide (T t)) := by
    intro u hu
    rw [List.mem_map] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    rw [mem_cardlist] at ht ⊢
    exact hmap t ht
  have := hnd2.length_le_of_subset hsub
  simpa using this

open Classical in
theorem card_eq_of_sub {S T : Fin p → Prop} (hsub : ∀ t, S t → T t) (hc : card T ≤ card S) :
    ∀ t, T t → S t := by
  intro t0 ht0
  apply Classical.byContradiction
  intro hn
  unfold card at hc
  have hnd : ((List.finRange p).filter (fun t => decide (S t))).Nodup :=
    List.Pairwise.filter _ (List.nodup_finRange p)
  have hnd2 : (t0 :: (List.finRange p).filter (fun t => decide (S t))).Nodup := by
    rw [List.nodup_cons]
    exact ⟨fun h => hn ((mem_cardlist).1 h), hnd⟩
  have hsub2 : (t0 :: (List.finRange p).filter (fun t => decide (S t)))
      ⊆ (List.finRange p).filter (fun t => decide (T t)) := by
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact (mem_cardlist).2 ht0
    · exact (mem_cardlist).2 (hsub u ((mem_cardlist).1 hu))
  have := hnd2.length_le_of_subset hsub2
  simp only [List.length_cons] at this
  omega

open Classical in
theorem card_pos {S : Fin p → Prop} {t0 : Fin p} (h : S t0) : 1 ≤ card S := by
  unfold card
  exact List.length_pos_of_mem ((mem_cardlist).2 h)

theorem card_congr {S T : Fin p → Prop} (h : ∀ t, S t ↔ T t) : card S = card T := by
  have : S = T := funext (fun t => propext (h t))
  rw [this]

end Counting

/-! ## Part 5. Affine labels t ↦ s·t + b on `Fin p`. -/
section Affine
variable (p : Nat) [NeZero p]

abbrev Aff := Fin p × Fin p

def aapp (f : Aff p) (t : Fin p) : Fin p := f.1 * t + f.2
def athen (f g : Aff p) : Aff p := (g.1 * f.1, g.1 * f.2 + g.2)
noncomputable def ainv (f : Aff p) : Aff p := (finv p f.1, -(finv p f.1 * f.2))

theorem athen_app (f g : Aff p) (t : Fin p) :
    aapp p (athen p f g) t = aapp p g (aapp p f t) := by
  unfold aapp athen; grind

theorem athen_assoc (f g h : Aff p) :
    athen p (athen p f g) h = athen p f (athen p g h) := by
  unfold athen; apply Prod.ext <;> simp only <;> grind

theorem athen_one_left (g : Aff p) : athen p ((1 : Fin p), (0 : Fin p)) g = g := by
  unfold athen; apply Prod.ext <;> simp only <;> grind

theorem athen_one_right (f : Aff p) : athen p f ((1 : Fin p), (0 : Fin p)) = f := by
  unfold athen; apply Prod.ext <;> simp only <;> grind

theorem ainv_app [PField p] (f : Aff p) (hf : f.1 ≠ 0) (t : Fin p) :
    aapp p (ainv p f) (aapp p f t) = t := by
  have h := mul_finv' p hf
  unfold aapp ainv; simp only; grind

theorem ainv_ainv [PField p] (f : Aff p) (hf : f.1 ≠ 0) : ainv p (ainv p f) = f := by
  have h := mul_finv' p hf
  have hi : finv p f.1 ≠ 0 := by
    intro h0
    rw [h0] at h
    have e1 : (1 : Fin p) = 0 := by grind
    apply hf
    calc f.1 = f.1 * 1 := by grind
      _ = f.1 * 0 := by rw [e1]
      _ = 0 := by grind
  have h2 := mul_finv' p hi
  have e : finv p (finv p f.1) = f.1 := by grind
  unfold ainv; simp only [e]
  apply Prod.ext <;> simp only <;> grind

theorem ainv_athen [PField p] (f g : Aff p) (hf : f.1 ≠ 0) (hg : g.1 ≠ 0) :
    ainv p (athen p f g) = athen p (ainv p g) (ainv p f) := by
  have h1 := mul_finv' p hf
  have h2 := mul_finv' p hg
  have hfg : g.1 * f.1 ≠ 0 := by
    intro h0
    have : (g.1 * f.1) * (finv p g.1 * finv p f.1) = 1 := by grind
    rw [h0] at this
    have e1 : (1 : Fin p) = 0 := by grind
    apply hf
    calc f.1 = f.1 * 1 := by grind
      _ = f.1 * 0 := by rw [e1]
      _ = 0 := by grind
  have h3 := mul_finv' p hfg
  have e : finv p (g.1 * f.1) = finv p g.1 * finv p f.1 := by grind
  unfold athen ainv; simp only [e]
  apply Prod.ext <;> simp only <;> grind

theorem aapp_inj (f : Aff p) (hu : ∃ b : Fin p, f.1 * b = 1) : Function.Injective (aapp p f) := by
  intro a b hab
  obtain ⟨c, hc⟩ := hu
  unfold aapp at hab
  grind

end Affine

/-! ## Part 6. Edges D and U, walks, and the holonomy group. -/
section Walks
variable (p : Nat) [NeZero p]

theorem one_ne_zero_fin (hp5 : 5 ≤ p) : (1 : Fin p) ≠ 0 := by
  intro h
  have : cs p 1 = cs p 0 := h
  rw [cs_eq_iff, Nat.mod_eq_of_lt (by omega), Nat.zero_mod] at this
  omega

theorem finv3_mul [PField p] (hp5 : 5 ≤ p) : (3 : Fin p) * finv p 3 = 1 :=
  mul_finv' p (three_ne_zero_fin p hp5)

theorem finv3_ne (hp5 : 5 ≤ p) [PField p] : finv p (3 : Fin p) ≠ 0 := by
  intro h0
  have h := finv3_mul p hp5
  rw [h0] at h
  have e1 : (1 : Fin p) = 0 := by grind
  exact one_ne_zero_fin p hp5 e1

inductive Edge (K : Nat) : Nat × Nat → Nat × Nat → Aff p → Prop
  | D {c f : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
      Edge K (c, f) ((2 * c) % 3 ^ (K + 1), 0) ((2 : Fin p), 0)
  | U {e : Nat} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
      Edge K (e % 3 ^ (K + 1), 0) (((e - 1) / 3) % 3 ^ (K + 1), 1)
        (finv p (3 : Fin p), -(finv p (3 : Fin p)))

inductive Walk (K : Nat) : Nat × Nat → Nat × Nat → Aff p → Prop
  | nil (c : Nat × Nat) : Walk K c c (1, 0)
  | fwd {u w d : Nat × Nat} {f g : Aff p} :
      Edge p K u w f → Walk K w d g → Walk K u d (athen p f g)
  | bwd {u w d : Nat × Nat} {f g : Aff p} :
      Edge p K u w f → Walk K u d g → Walk K w d (athen p (ainv p f) g)

def base : Nat × Nat := (1, 0)

def Hol (K : Nat) : Aff p → Prop := fun f => Walk p K base base f

def HasTranslation (K : Nat) : Prop :=
  ∃ d : Fin p, d ≠ 0 ∧ Hol p K ((1 : Fin p), d)

theorem Walk.append {K : Nat} {u w d : Nat × Nat} {f g : Aff p}
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

theorem Edge.label_unit [PField p] (hp5 : 5 ≤ p) {K : Nat} {u w : Nat × Nat} {f : Aff p}
    (h : Edge p K u w f) : f.1 ≠ 0 := by
  cases h with
  | D hc hlt hf => exact two_ne_zero_fin p hp5
  | U h1 h9 hlt => exact finv3_ne p hp5

theorem Edge.src_valid {K : Nat} {u w : Nat × Nat} {f : Aff p} (h : Edge p K u w f) :
    u.1 % 3 ≠ 0 ∧ u.1 < 3 ^ (K + 1) ∧ u.2 < 2 := by
  cases h with
  | D hc hlt hf => exact ⟨hc, hlt, hf⟩
  | U h1 h9 hlt =>
    exact ⟨mod_unit (three_dvd_pow K) (by omega), Nat.mod_lt _ (by have := one_lt_pow3 K; omega), by omega⟩

theorem Walk.label_unit [PField p] (hp5 : 5 ≤ p) {K : Nat} {u w : Nat × Nat} {f : Aff p}
    (h : Walk p K u w f) : f.1 ≠ 0 := by
  induction h with
  | nil c => exact one_ne_zero_fin p hp5
  | @fwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have hf' := mul_finv' p hf
    have hg' := mul_finv' p ih
    intro h0
    simp only [athen] at h0
    have : (g.1 * f.1) * (finv p g.1 * finv p f.1) = 1 := by grind
    rw [h0] at this
    have e1 : (1 : Fin p) = 0 := by grind
    exact one_ne_zero_fin p hp5 (by grind)
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have hf' := mul_finv' p hf
    have hg' := mul_finv' p ih
    intro h0
    simp only [athen, ainv] at h0
    have : (g.1 * finv p f.1) * (f.1 * finv p g.1) = 1 := by grind
    rw [h0] at this
    exact one_ne_zero_fin p hp5 (by grind)

theorem Walk.symm [PField p] (hp5 : 5 ≤ p) {K : Nat} {u w : Nat × Nat} {f : Aff p}
    (h : Walk p K u w f) : Walk p K w u (ainv p f) := by
  induction h with
  | nil c =>
    have e : ainv p ((1 : Fin p), (0 : Fin p)) = (1, 0) := by
      unfold ainv
      have h1 : (1 : Fin p) * finv p 1 = 1 := mul_finv' p (one_ne_zero_fin p hp5)
      apply Prod.ext <;> simp only <;> grind
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
      have h1 := mul_finv' p hf
      intro h0
      simp only [ainv] at h0
      rw [h0] at h1
      exact one_ne_zero_fin p hp5 (by grind)
    have key := Walk.append p ih (Walk.fwd he (Walk.nil w))
    have e : ainv p (athen p (ainv p f) g)
        = athen p (ainv p g) (athen p f (1, 0)) := by
      rw [athen_one_right, ainv_athen p (ainv p f) g hfi hg, ainv_ainv p f hf]
    rw [e]; exact key

theorem Hol_mul {K : Nat} {f g : Aff p}
    (hf : Hol p K f) (hg : Hol p K g) : Hol p K (athen p f g) := Walk.append p hf hg

theorem Hol_inv [PField p] (hp5 : 5 ≤ p) {K : Nat} {f : Aff p}
    (hf : Hol p K f) : Hol p K (ainv p f) := Walk.symm p hp5 hf

end Walks

/-! ## Part 7a. Fibres and their cardinalities. -/
section Fibres
variable (p : Nat) [NeZero p]

def fibre (K v c f : Nat) : Fin p → Prop :=
  fun t => ∃ n, Tree v n ∧ n % 3 ^ (K + 1) = c ∧ n % 2 = f ∧ cs p n = t

def Img (f : Aff p) (S : Fin p → Prop) : Fin p → Prop := fun t => ∃ s, S s ∧ aapp p f s = t

theorem mul2_inj [PField p] (hp5 : 5 ≤ p) {a b : Fin p} (h : (2 : Fin p) * a = 2 * b) : a = b := by
  exact cancel_unit p (mul_finv' p (two_ne_zero_fin p hp5)) h

theorem fibre_proj {J K v c f : Nat} (hJK : J ≤ K) {t : Fin p} (ht : fibre p K v c f t) :
    fibre p J v (c % 3 ^ (J + 1)) f t := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨n, hn, ?_, hf, hnt⟩
  rw [← hc, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (by omega))]

theorem fibre_D_image {K v c f : Nat} {t : Fin p} (ht : fibre p K v c f t) :
    fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 (2 * t) := by
  obtain ⟨n, hn, hc, hf, hnt⟩ := ht
  refine ⟨2 * n, Tree.D hn, ?_, by omega, by rw [← hnt, cs_mul, cs_two]⟩
  subst hc
  exact (Nat.mul_mod_mod 2 n _).symm

theorem fibre_D_card_le [PField p] (hp5 : 5 ≤ p) (K v c f : Nat) :
    card (fibre p K v c f) ≤ card (fibre p K v ((2 * c) % 3 ^ (K + 1)) 0) :=
  card_le_of_inj (fun t => 2 * t) (fun _ _ h => mul2_inj p hp5 h) (fun _ ht => fibre_D_image p ht)

theorem fibre_card_iter [PField p] (hp5 : 5 ≤ p) (K v : Nat) :
    ∀ (j c : Nat), c < 3 ^ (K + 1) → c % 3 ≠ 0 →
      card (fibre p K v c 0) ≤ card (fibre p K v ((2 ^ j * c) % 3 ^ (K + 1)) 0) := by
  intro j
  induction j with
  | zero =>
    intro c hc _
    have h0 : (2 ^ 0 * c) % 3 ^ (K + 1) = c := by
      rw [Nat.pow_zero, Nat.one_mul]; exact Nat.mod_eq_of_lt hc
    rw [h0]; exact Nat.le_refl _
  | succ j ih =>
    intro c hc hc3
    have h1 := fibre_D_card_le p hp5 K v c 0
    have hd3 : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 := mod_unit (three_dvd_pow K) (by omega)
    have h2 := ih ((2 * c) % 3 ^ (K + 1)) (Nat.mod_lt _ (by have := one_lt_pow3 K; omega)) hd3
    have e : (2 ^ j * ((2 * c) % 3 ^ (K + 1))) % 3 ^ (K + 1)
        = (2 ^ (j + 1) * c) % 3 ^ (K + 1) := by
      rw [Nat.mul_mod_mod, Nat.pow_succ]; congr 1; grind
    rw [e] at h2
    exact Nat.le_trans h1 h2

theorem fibre_card_const [PField p] (hp5 : 5 ≤ p) {K v c d : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) (hd : d % 3 ≠ 0) (hdl : d < 3 ^ (K + 1)) :
    card (fibre p K v c 0) = card (fibre p K v d 0) := by
  obtain ⟨j, hj⟩ := two_transitive hc hd hdl
  obtain ⟨i, hi⟩ := two_transitive hd hc hcl
  have h1 := fibre_card_iter p hp5 K v j c hcl hc
  have h2 := fibre_card_iter p hp5 K v i d hdl hd
  rw [hj] at h1
  rw [hi] at h2
  exact Nat.le_antisymm h1 h2

end Fibres

/-! ## Part 7b. Doubling and undo on fibres; sizes sigma_K. -/
section Fibres2
variable (p : Nat) [NeZero p]

theorem fibre_D_eq [PField p] (hp5 : 5 ≤ p) {K v c : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    ∀ t, fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 t ↔ ∃ s, fibre p K v c 0 s ∧ 2 * s = t := by
  have hd : (2 * c) % 3 ^ (K + 1) % 3 ≠ 0 := mod_unit (three_dvd_pow K) (by omega)
  have hlt : (2 * c) % 3 ^ (K + 1) < 3 ^ (K + 1) :=
    Nat.mod_lt _ (by have := one_lt_pow3 K; omega)
  have hcard := fibre_card_const p hp5 (v := v) hd hlt hc hcl
  have hle : card (fibre p K v ((2 * c) % 3 ^ (K + 1)) 0)
      ≤ card (fun t => ∃ s, fibre p K v c 0 s ∧ 2 * s = t) := by
    rw [hcard]
    exact card_le_of_inj (fun t => 2 * t) (fun a b h => mul2_inj p hp5 h) (fun t ht => ⟨t, ht, rfl⟩)
  intro t
  constructor
  · intro ht
    exact card_eq_of_sub (S := fun t => ∃ s, fibre p K v c 0 s ∧ 2 * s = t)
      (T := fibre p K v ((2 * c) % 3 ^ (K + 1)) 0)
      (fun t ⟨s, hs, e⟩ => by rw [← e]; exact fibre_D_image p hs) hle t ht
  · rintro ⟨s, hs, rfl⟩
    exact fibre_D_image p hs

theorem fibre_flag1_sub [PField p] (hp5 : 5 ≤ p) {K v c : Nat}
    (hc : c % 3 ≠ 0) (hcl : c < 3 ^ (K + 1)) :
    ∀ t, fibre p K v c 1 t → fibre p K v c 0 t := by
  intro t ht
  have h1 := fibre_D_image p ht
  obtain ⟨t', ht', e⟩ := (fibre_D_eq p hp5 hc hcl _).1 h1
  have : t' = t := mul2_inj p hp5 e
  rw [this] at ht'; exact ht'

theorem fibre_U_iff [PField p] (hp5 : 5 ≤ p) {K v t0 : Nat} (hv : v % 2 = 0)
    (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) (t : Fin p) :
    fibre p K v t0 1 t ↔
      fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0 (3 * t + 1) := by
  have hpow : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
  constructor
  · rintro ⟨n, hn, hc, hf, hnt⟩
    obtain ⟨m, hm, h6, h3, hnm⟩ := tree_odd_inv hv hn hf
    have hm3 : m = 3 * n + 1 := by omega
    refine ⟨m, hm, ?_, by omega, ?_⟩
    · have hq := Nat.div_add_mod n (3 ^ (K + 1))
      rw [hc] at hq
      have e : m = (3 * t0 + 1) + 3 ^ (K + 1 + 1) * (n / 3 ^ (K + 1)) := by
        rw [hm3, hpow]; grind
      rw [e, Nat.add_mul_mod_self_left]
    · rw [hm3, cs_add, cs_mul, cs_three, cs_one, hnt]
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
    · have hcm : cs p m = 3 * cs p n + 1 := by
        rw [hm', cs_add, cs_mul, cs_three, cs_one]
      exact cancel_unit p (finv3_mul p hp5) (by
        calc (3 : Fin p) * cs p n = (3 * cs p n + 1) - 1 := by grind
          _ = (3 * t + 1) - 1 := by rw [← hcm, hmt]
          _ = 3 * t := by grind)

noncomputable def sig (K v : Nat) : Nat := card (fibre p K v 1 0)

theorem sig_antitone (K v : Nat) : sig p (K + 1) v ≤ sig p K v := by
  unfold sig
  apply card_le_of_inj (fun t => t) (fun a b h => h)
  intro t ht
  have h := fibre_proj p (Nat.le_succ K) ht
  rwa [Nat.mod_eq_of_lt (one_lt_pow3 K)] at h

theorem sig_pos [PField p] (hp5 : 5 ≤ p) {v : Nat} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (K : Nat) : 1 ≤ sig p K v := by
  have hlt : 1 < 3 ^ (K + 1) := one_lt_pow3 K
  have hne : fibre p K v (v % 3 ^ (K + 1)) 0 (cs p v) := ⟨v, Tree.seed, rfl, hv, rfl⟩
  have hpos := card_pos hne
  have heq := fibre_card_const p hp5 (v := v) (K := K) (mod_unit (three_dvd_pow K) hv3)
    (Nat.mod_lt _ (by omega)) (by omega : 1 % 3 ≠ 0) hlt
  unfold sig; omega

theorem fibre1_card [PField p] (hp5 : 5 ≤ p) {K v t0 : Nat} (hv : v % 2 = 0) (_hv3 : v % 3 ≠ 0)
    (ht0 : t0 % 3 ≠ 0) (ht0l : t0 < 3 ^ (K + 1)) :
    card (fibre p K v t0 1) = sig p (K + 1) v := by
  have h3 := finv3_mul p hp5
  have hle1 : card (fibre p K v t0 1)
      ≤ card (fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0) := by
    apply card_le_of_inj (fun t => 3 * t + 1)
    · intro a b h
      exact cancel_unit p h3 (by grind)
    · intro t ht
      exact (fibre_U_iff p hp5 hv ht0 ht0l t).1 ht
  have hle2 : card (fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0)
      ≤ card (fibre p K v t0 1) := by
    apply card_le_of_inj (fun a => finv p 3 * (a - 1))
    · intro a b h
      have e : ∀ x : Fin p, 3 * (finv p 3 * (x - 1)) + 1 = x := by
        intro x
        calc 3 * (finv p 3 * (x - 1)) + 1 = (3 * finv p 3) * (x - 1) + 1 := by grind
          _ = (x - 1) + 1 := by rw [h3]; grind
          _ = x := by grind
      have : 3 * (finv p 3 * (a - 1)) + 1 = 3 * (finv p 3 * (b - 1)) + 1 := by rw [h]
      rw [e a, e b] at this; exact this
    · intro a ha
      apply (fibre_U_iff p hp5 hv ht0 ht0l _).2
      have e : 3 * (finv p 3 * (a - 1)) + 1 = a := by
        calc 3 * (finv p 3 * (a - 1)) + 1 = (3 * finv p 3) * (a - 1) + 1 := by grind
          _ = (a - 1) + 1 := by rw [h3]; grind
          _ = a := by grind
      rw [e]; exact ha
  have hc := fibre_card_const p hp5 (K := K + 1) (v := v)
    (mod_unit (three_dvd_pow (K + 1)) (by omega) : ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) % 3 ≠ 0)
    (Nat.mod_lt _ (by have := one_lt_pow3 (K + 1); omega)) (by omega : 1 % 3 ≠ 0)
    (one_lt_pow3 (K + 1))
  have : card (fibre p K v t0 1) = card (fibre p (K + 1) v ((3 * t0 + 1) % 3 ^ (K + 1 + 1)) 0) :=
    Nat.le_antisymm hle1 hle2
  rw [this, hc]; rfl

end Fibres2

/-! ## Part 7c. Stabilisation, and the action of edges and walks on stabilised fibres. -/
section Stabil
variable (p : Nat) [NeZero p]

theorem stabilize_nat : ∀ n : Nat, ∀ f : Nat → Nat, (∀ k, f (k + 1) ≤ f k) → f 0 ≤ n →
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

def Stab (v K0 : Nat) : Prop :=
  ∀ K, K0 ≤ K → 1 ≤ K →
    (∀ c, c % 3 ≠ 0 → c < 3 ^ (K + 1) → ∀ t, fibre p K v c 1 t ↔ fibre p K v c 0 t) ∧
    (∀ e, e % 3 ≠ 0 → e < 3 ^ (K + 2) →
      ∀ t, fibre p (K + 1) v e 0 t ↔ fibre p K v (e % 3 ^ (K + 1)) 0 t)

theorem stabilization [PField p] (hp5 : 5 ≤ p) {v : Nat} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0) :
    ∃ K0, 1 ≤ K0 ∧ Stab p v K0 := by
  obtain ⟨K0', hK0'⟩ := stabilize_nat (sig p 1 v) (fun k => sig p (k + 1) v)
    (fun k => sig_antitone p (k + 1) v) (Nat.le_refl _)
  have hconst : ∀ K, K0' + 1 ≤ K → sig p K v = sig p (K0' + 1) v := by
    intro K hK
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    exact hK0' k (by omega)
  have hK0 : 1 ≤ K0' + 1 := by omega
  refine ⟨K0' + 1, hK0, ?_⟩
  intro K hK hK1
  have hσK := hconst K hK
  have hσK1 := hconst (K + 1) (by omega)
  constructor
  · intro c hc hcl t
    have c1 : card (fibre p K v c 1) = sig p (K + 1) v :=
      fibre1_card p hp5 hv hv3 hc hcl
    have c0 : card (fibre p K v c 0) = sig p K v :=
      fibre_card_const p hp5 hc hcl (by omega : 1 % 3 ≠ 0) (one_lt_pow3 K)
    have h := card_eq_of_sub (S := fibre p K v c 1) (T := fibre p K v c 0)
      (fibre_flag1_sub p hp5 hc hcl) (by omega)
    exact ⟨fibre_flag1_sub p hp5 hc hcl t, h t⟩
  · intro e he hel t
    have hsub : ∀ t, fibre p (K + 1) v e 0 t → fibre p K v (e % 3 ^ (K + 1)) 0 t :=
      fun t ht => fibre_proj p (Nat.le_succ K) ht
    have c1 : card (fibre p (K + 1) v e 0) = sig p (K + 1) v :=
      fibre_card_const p hp5 he hel (by omega : 1 % 3 ≠ 0) (one_lt_pow3 (K + 1))
    have c0 : card (fibre p K v (e % 3 ^ (K + 1)) 0) = sig p K v :=
      fibre_card_const p hp5 (mod_unit (three_dvd_pow K) he)
        (Nat.mod_lt _ (by have := one_lt_pow3 K; omega)) (by omega : 1 % 3 ≠ 0) (one_lt_pow3 K)
    have h := card_eq_of_sub (S := fibre p (K + 1) v e 0)
      (T := fibre p K v (e % 3 ^ (K + 1)) 0) hsub (by omega)
    exact ⟨hsub t, h t⟩

omit [NeZero p] in
theorem Img_congr (f : Aff p) {S S' : Fin p → Prop} (h : ∀ s, S s ↔ S' s) :
    ∀ t, Img p f S t ↔ Img p f S' t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩; exact ⟨s, (h s).1 hs, e⟩
  · rintro ⟨s, hs, e⟩; exact ⟨s, (h s).2 hs, e⟩

theorem Img_athen (f g : Aff p) (S : Fin p → Prop) :
    ∀ t, Img p (athen p f g) S t ↔ Img p g (Img p f S) t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩
    exact ⟨aapp p f s, ⟨s, hs, rfl⟩, by rw [← athen_app]; exact e⟩
  · rintro ⟨s', ⟨s, hs, e1⟩, e2⟩
    exact ⟨s, hs, by rw [athen_app, e1]; exact e2⟩

theorem Img_nil (S : Fin p → Prop) : ∀ t, Img p ((1 : Fin p), (0 : Fin p)) S t ↔ S t := by
  intro t; constructor
  · rintro ⟨s, hs, e⟩
    have : aapp p ((1 : Fin p), (0 : Fin p)) s = s := by unfold aapp; simp only; grind
    rw [this] at e; rw [← e]; exact hs
  · intro h
    exact ⟨t, h, by unfold aapp; simp only; grind⟩

theorem edge_image [PField p] (hp5 : 5 ≤ p) {v K0 K : Nat} (hv : v % 2 = 0) (_hv3 : v % 3 ≠ 0)
    (hS : Stab p v K0) (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : Nat × Nat} {f : Aff p}
    (h : Edge p K u w f) :
    ∀ t, Img p f (fibre p K v u.1 u.2) t ↔ fibre p K v w.1 w.2 t := by
  cases h with
  | @D c f0 hc hlt hf0 =>
    have h1 : ∀ t, fibre p K v c f0 t ↔ fibre p K v c 0 t := by
      intro t
      have hcase : f0 = 0 ∨ f0 = 1 := by omega
      rcases hcase with rfl | rfl
      · exact Iff.rfl
      · exact (hS K hK hK1).1 c hc hlt t
    intro t
    have hfun : ∀ s : Fin p, aapp p ((2 : Fin p), (0 : Fin p)) s = 2 * s := by
      intro s; unfold aapp; simp only; grind
    refine (Img_congr p _ h1 t).trans ?_
    show (∃ s, fibre p K v c 0 s ∧ aapp p ((2 : Fin p), (0 : Fin p)) s = t) ↔
      fibre p K v ((2 * c) % 3 ^ (K + 1)) 0 t
    rw [fibre_D_eq p hp5 hc hlt t]
    constructor
    · rintro ⟨s, hs, e⟩; exact ⟨s, hs, by rw [← hfun s]; exact e⟩
    · rintro ⟨s, hs, e⟩; exact ⟨s, hs, by rw [hfun s]; exact e⟩
  | @U e h1 h9 hlt =>
    have hM : 3 ^ (K + 1 + 1) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
    have hM2 : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := hM
    have ht0 : ((e - 1) / 3) % 3 ^ (K + 1) = (e - 1) / 3 := Nat.mod_eq_of_lt (by omega)
    have hSb := (hS K hK hK1).2 e (by omega) hlt
    have h3 := finv3_mul p hp5
    show ∀ t, (∃ s, fibre p K v (e % 3 ^ (K + 1)) 0 s ∧
        aapp p (finv p (3 : Fin p), -(finv p (3 : Fin p))) s = t) ↔
      fibre p K v (((e - 1) / 3) % 3 ^ (K + 1)) 1 t
    rw [ht0]
    have he0 : (3 * ((e - 1) / 3) + 1) % 3 ^ (K + 1 + 1) = e := by
      rw [show 3 * ((e - 1) / 3) + 1 = e by omega]
      exact Nat.mod_eq_of_lt (by omega)
    have hiff := fibre_U_iff p hp5 hv (K := K) (t0 := (e - 1) / 3) (by omega) (by omega)
    have key : ∀ x : Fin p, 3 * (finv p 3 * x + -finv p 3) + 1 = x := by
      intro x
      calc 3 * (finv p 3 * x + -finv p 3) + 1 = (3 * finv p 3) * x - (3 * finv p 3) + 1 := by grind
        _ = x - 1 + 1 := by rw [h3]; grind
        _ = x := by grind
    intro t
    rw [hiff t, he0]
    constructor
    · rintro ⟨s, hs, e2⟩
      have hs' := (hSb s).2 hs
      have : 3 * t + 1 = s := by
        rw [← e2]; unfold aapp; simp only; exact key s
      rw [this]; exact hs'
    · intro ha
      refine ⟨3 * t + 1, (hSb _).1 ha, ?_⟩
      unfold aapp; simp only
      calc finv p 3 * (3 * t + 1) + -finv p 3 = (finv p 3 * 3) * t + finv p 3 - finv p 3 := by grind
        _ = t := by
          have h3' : finv p 3 * 3 = 1 := by rw [Lean.Grind.CommSemiring.mul_comm]; exact h3
          rw [h3']; grind

theorem walk_image [PField p] (hp5 : 5 ≤ p) {v K0 K : Nat} (hv : v % 2 = 0) (hv3 : v % 3 ≠ 0)
    (hS : Stab p v K0) (hK : K0 ≤ K) (hK1 : 1 ≤ K) {u w : Nat × Nat} {f : Aff p}
    (h : Walk p K u w f) :
    ∀ t, Img p f (fibre p K v u.1 u.2) t ↔ fibre p K v w.1 w.2 t := by
  induction h with
  | nil c => exact Img_nil p _
  | @fwd u w d f g he hw ih =>
    have e1 := edge_image p hp5 hv hv3 hS hK hK1 he
    intro t
    refine (Img_athen p f g _ t).trans ?_
    refine (Img_congr p g e1 t).trans ?_
    exact ih t
  | @bwd u w d f g he hw ih =>
    have hf := Edge.label_unit p hp5 he
    have e1 := edge_image p hp5 hv hv3 hS hK hK1 he
    have e2 : ∀ t, Img p (ainv p f) (fibre p K v w.1 w.2) t ↔ fibre p K v u.1 u.2 t := by
      intro t
      constructor
      · rintro ⟨s', hs', e⟩
        obtain ⟨s, hs, es⟩ := (e1 s').2 hs'
        rw [← e, ← es, ainv_app p f hf]; exact hs
      · intro ht
        exact ⟨aapp p f t, (e1 _).1 ⟨t, ht, rfl⟩, ainv_app p f hf t⟩
    intro t
    refine (Img_athen p (ainv p f) g _ t).trans ?_
    refine (Img_congr p g e2 t).trans ?_
    exact ih t

end Stabil

/-! ## Part 8a. Flat assignments: collapse, normalisation, Phi(2^j) = 2^j, powers of 4. -/
section FlatA
variable (p : Nat) [NeZero p]

def Flat (K : Nat) (Φ : Nat × Nat → Fin p) : Prop :=
  ∀ u w f, Edge p K u w f → Φ w = aapp p f (Φ u)

theorem aapp_two (x : Fin p) : aapp p ((2 : Fin p), (0 : Fin p)) x = 2 * x := by
  unfold aapp; simp only; grind

theorem flat_collapse [PField p] (hp5 : 5 ≤ p) {K : Nat} {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) {c : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) :
    Φ (c, 0) = Φ (c, 1) := by
  have h0 := hΦ _ _ _ (Edge.D (p := p) (f := 0) hc hlt (by omega))
  have h1 := hΦ _ _ _ (Edge.D (p := p) (f := 1) hc hlt (by omega))
  rw [aapp_two] at h0 h1
  exact cancel_unit p (mul_finv' p (two_ne_zero_fin p hp5)) (by rw [← h0, ← h1])

theorem flat_double [PField p] {K : Nat} {Φ : Nat × Nat → Fin p} (hΦ : Flat p K Φ)
    {c : Nat} (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) :
    Φ ((2 * c) % 3 ^ (K + 1), 0) = 2 * Φ (c, 0) := by
  have h0 := hΦ _ _ _ (Edge.D (p := p) (f := 0) hc hlt (by omega))
  rw [aapp_two] at h0; exact h0

theorem flat_U [PField p] (hp5 : 5 ≤ p) {K : Nat} {Φ : Nat × Nat → Fin p} (hΦ : Flat p K Φ)
    {e : Nat} (h1 : e % 3 = 1) (h9 : e % 9 ≠ 1) (hlt : e < 3 ^ (K + 2)) :
    3 * Φ (((e - 1) / 3) % 3 ^ (K + 1), 1) = Φ (e % 3 ^ (K + 1), 0) - 1 := by
  have he := hΦ _ _ _ (Edge.U (p := p) (K := K) (e := e) h1 h9 hlt)
  have h3 := finv3_mul p hp5
  unfold aapp at he; simp only at he
  rw [he]
  calc 3 * (finv p 3 * Φ (e % 3 ^ (K + 1), 0) + -finv p 3)
      = (3 * finv p 3) * Φ (e % 3 ^ (K + 1), 0) - (3 * finv p 3) := by grind
    _ = Φ (e % 3 ^ (K + 1), 0) - 1 := by rw [h3]; grind

theorem flat_one [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) : Φ (1, 0) = 1 := by
  have hM : 9 ≤ 3 ^ (K + 1) := by
    calc 9 = 3 ^ 2 := by decide
      _ ≤ 3 ^ (K + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hM2 : 3 ^ (K + 1) ≤ 3 ^ (K + 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have u := flat_U p hp5 hΦ (e := 4) (by omega) (by omega) (by omega)
  have h4 : 4 % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  have h1m : 1 % 3 ^ (K + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hc : (4 - 1) / 3 = 1 := by decide
  rw [hc, h1m, h4] at u
  have d1 := flat_double p hΦ (c := 1) (by omega) (by omega)
  have d2 := flat_double p hΦ (c := 2) (by omega) (by omega)
  have m2 : (2 * 1) % 3 ^ (K + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  have m4 : (2 * 2) % 3 ^ (K + 1) = 4 := Nat.mod_eq_of_lt (by omega)
  rw [m2] at d1
  rw [m4] at d2
  have hcol := flat_collapse p hp5 hΦ (c := 1) (by omega) (by omega)
  rw [← hcol, d2, d1] at u
  -- u : 3 * Φ(1,0) = 2 * (2 * Φ(1,0)) - 1
  calc Φ (1, 0) = 4 * Φ (1, 0) - 3 * Φ (1, 0) := by grind
    _ = 4 * Φ (1, 0) - (2 * (2 * Φ (1, 0)) - 1) := by rw [u]
    _ = 1 := by grind

theorem cs_two_pow_unit [PField p] (hp5 : 5 ≤ p) (j : Nat) : ∃ b : Fin p, cs p (2 ^ j) * b = 1 := by
  induction j with
  | zero => exact ⟨1, by rw [Nat.pow_zero, cs_one]; grind⟩
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨finv p 2 * b, ?_⟩
    have h2 := mul_finv' p (two_ne_zero_fin p hp5)
    rw [Nat.pow_succ, cs_mul, cs_two]
    calc cs p (2 ^ j) * 2 * (finv p 2 * b) = (2 * finv p 2) * (cs p (2 ^ j) * b) := by grind
      _ = 1 := by rw [h2, hb]; grind

theorem flat_hom [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) : ∀ j : Nat, Φ ((2 ^ j) % 3 ^ (K + 1), 0) = cs p (2 ^ j) := by
  intro j
  induction j with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K), cs_one]
    exact flat_one p hp5 hK hΦ
  | succ j ih =>
    have hc : (2 ^ j % 3 ^ (K + 1)) % 3 ≠ 0 :=
      mod_unit (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt : 2 ^ j % 3 ^ (K + 1) < 3 ^ (K + 1) :=
      Nat.mod_lt _ (by have := one_lt_pow3 K; omega)
    have h1 := flat_double p hΦ hc hlt
    rw [ih] at h1
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.mul_mod_mod, e2]
    rw [e] at h1
    rw [h1, Nat.pow_succ, Nat.mul_comm, cs_mul, cs_two]

theorem flat_four_form [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) {c : Nat} (hc : c % 3 = 1) (hlt : c < 3 ^ (K + 1)) :
    ∃ e : Nat, (4 ^ e) % 3 ^ (K + 1) = c ∧ Φ (c, 0) = cs p (4 ^ e) := by
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
  have hf := flat_hom p hp5 hK hΦ (2 * e)
  rw [hj, h4e] at hf
  exact hf

end FlatA

/-! ## Part 8b. The order of 4 modulo p, stated on exponents. -/
section FlatB
variable (p : Nat) [NeZero p]

/-! ### The order of 4 modulo p, stated on exponents -/

def Q (m : Nat) : Prop := cs p (4 ^ m) = 1

theorem Q_add {m n : Nat} (hm : Q p m) (hn : Q p n) : Q p (m + n) := by
  unfold Q at *
  rw [Nat.pow_add, cs_mul, hm, hn]; grind

theorem Q_mul_left {n : Nat} (hn : Q p n) : ∀ q, Q p (n * q) := by
  intro q
  induction q with
  | zero => unfold Q; rw [Nat.mul_zero, Nat.pow_zero, cs_one]
  | succ q ih => rw [Nat.mul_succ]; exact Q_add p ih hn

theorem Q_cancel {m n : Nat} (hn : Q p n) (h : Q p (m + n)) : Q p m := by
  unfold Q at *
  rw [Nat.pow_add, cs_mul, hn] at h
  rw [← h]; grind

theorem Q_mod {m n : Nat} (hn : Q p n) (hm : Q p m) : Q p (m % n) := by
  have h := Nat.mod_add_div m n
  have h2 : Q p (m % n + n * (m / n)) := by rw [h]; exact hm
  exact Q_cancel p (Q_mul_left p hn (m / n)) h2

theorem Q_gcd : ∀ m n : Nat, Q p m → Q p n → Q p (Nat.gcd m n) := by
  intro m n
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; rw [Nat.gcd_zero_left]; exact hn
  | H1 m n hm ih =>
    intro h1 h2
    rw [Nat.gcd_rec]
    exact ih (Q_mod p h1 h2) h1

theorem dvd_pow3 : ∀ n d : Nat, d ∣ 3 ^ n → ∃ b, b ≤ n ∧ d = 3 ^ b := by
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

theorem exists_min_pow3 : ∀ n : Nat, Q p (3 ^ n) →
    ∃ a, a ≤ n ∧ Q p (3 ^ a) ∧ ∀ b, b < a → ¬ Q p (3 ^ b) := by
  have key : ∀ N n : Nat, n ≤ N → Q p (3 ^ n) →
      ∃ a, a ≤ n ∧ Q p (3 ^ a) ∧ ∀ b, b < a → ¬ Q p (3 ^ b) := by
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
      · by_cases hex : ∃ b, b < n ∧ Q p (3 ^ b)
        · obtain ⟨b, hb, hQ⟩ := hex
          obtain ⟨a, ha, h1, h2⟩ := ih b (by omega) hQ
          exact ⟨a, by omega, h1, h2⟩
        · exact ⟨n, Nat.le_refl _, h, fun b hb hQ => hex ⟨b, hb, hQ⟩⟩
  intro n h
  exact key n n (Nat.le_refl _) h

theorem order_pow3 {n : Nat} (h : Q p (3 ^ n)) : ∃ a, a ≤ n ∧ ∀ m, Q p m ↔ 3 ^ a ∣ m := by
  obtain ⟨a, han, hQa, hmin⟩ := exists_min_pow3 p n h
  refine ⟨a, han, fun m => ⟨fun hm => ?_, fun ⟨q, hq⟩ => ?_⟩⟩
  · have hg := Q_gcd p m (3 ^ n) hm h
    obtain ⟨b, hb, hgb⟩ := dvd_pow3 n _ (Nat.gcd_dvd_right m (3 ^ n))
    rw [hgb] at hg
    have hab : a ≤ b := by
      apply Classical.byContradiction
      intro hlt
      exact hmin b (by omega) hg
    have : 3 ^ a ∣ 3 ^ b := Nat.pow_dvd_pow 3 hab
    rw [← hgb] at this
    exact Nat.dvd_trans this (Nat.gcd_dvd_left m (3 ^ n))
  · rw [hq]; exact Q_mul_left p hQa q

theorem three_pow_odd (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

end FlatB

/-! ## Part 8c. No flat assignment exists (the arithmetic obstruction). -/
section FlatC
variable (p : Nat) [NeZero p]

theorem flat_four_pow [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) : cs p (4 ^ (3 ^ (K - 1))) = 1 := by
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
  have h3 := finv3_mul p hp5
  have hc4 := four_pow_cong (K := n + 1) (by omega)
  rw [hsub, ← hs, hMs, hKs] at hc4
  have h4' : 4 ^ s % (9 * s) = 1 + 3 * s := by
    rw [hc4]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨y, hy⟩ : ∃ y, 2 * y + 1 = 9 * s := ⟨(9 * s - 1) / 2, by omega⟩
  have hy_lt : y < 9 * s := by omega
  have hy3 : y % 3 = 1 := by omega
  have hy9 : y % 9 = 4 := by omega
  have hcy := flat_collapse p hp5 hΦ (c := y) (by omega) (by rw [hMs]; exact hy_lt)
  have m0 : y % 3 ^ (n + 1 + 1) = y := by rw [hMs]; exact Nat.mod_eq_of_lt hy_lt
  have u1 := flat_U p hp5 hΦ (e := y + 9 * s) (by omega) (by omega) (by rw [h3K2]; omega)
  have t1 : (y + 9 * s - 1) / 3 = y := by omega
  have m1 : (y + 9 * s) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mod_right]; exact Nat.mod_eq_of_lt hy_lt
  rw [t1, m0, m1] at u1
  have u2 := flat_U p hp5 hΦ (e := y + 9 * s * 2) (by omega) (by omega) (by rw [h3K2]; omega)
  have t2 : (y + 9 * s * 2 - 1) / 3 = y + 3 * s := by omega
  have hy3s : y + 3 * s < 9 * s := by omega
  have m3 : (y + 3 * s) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    rw [hMs]; exact Nat.mod_eq_of_lt hy3s
  have m2 : (y + 9 * s * 2) % 3 ^ (n + 1 + 1) = y := by
    rw [hMs, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hy_lt
  rw [t2, m3, m2] at u2
  have hcy2 := flat_collapse p hp5 hΦ (c := y + 3 * s) (by omega) (by rw [hMs]; exact hy3s)
  rw [← hcy] at u1
  have hB : Φ (y + 3 * s, 1) = Φ (y, 0) := cancel_unit p h3 (u2.trans u1.symm)
  have hC0 : Φ (y + 3 * s, 0) = Φ (y, 0) := hcy2.trans hB
  obtain ⟨j, hj⟩ := two_transitive (K := n + 1) (c := 1) (d := y) (by omega) (by omega)
    (by rw [hMs]; exact hy_lt)
  rw [Nat.mul_one] at hj
  have hj' : 2 ^ j % (9 * s) = y := by rw [← hMs]; exact hj
  have hfy := flat_hom p hp5 (K := n + 1) (by omega) hΦ j
  rw [hj] at hfy
  have hmod : (2 ^ (j + 2 * s)) % 3 ^ (n + 1 + 1) = y + 3 * s := by
    have e : 2 ^ (j + 2 * s) = 2 ^ j * 4 ^ s := by
      rw [Nat.pow_add, Nat.pow_mul]
    obtain ⟨m, hm⟩ : ∃ m, y = 3 * m + 1 := ⟨y / 3, by omega⟩
    have hprod : y * (1 + 3 * s) = (y + 3 * s) + 9 * s * m := by
      rw [hm]; grind
    rw [hMs, e, Nat.mul_mod, hj', h4', hprod, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hy3s
  have hf2 := flat_hom p hp5 (K := n + 1) (by omega) hΦ (j + 2 * s)
  rw [hmod] at hf2
  have hpow : cs p (2 ^ (j + 2 * s)) = cs p (2 ^ j) := hf2.symm.trans (hC0.trans hfy)
  obtain ⟨b, hb⟩ := cs_two_pow_unit p hp5 j
  have h2 : cs p (2 ^ j) * cs p (2 ^ (2 * s)) = cs p (2 ^ j) * 1 := by
    rw [← cs_mul, ← Nat.pow_add]
    rw [hpow]; grind
  have h2' := cancel_unit p hb h2
  have e4 : 4 ^ s = 2 ^ (2 * s) := by rw [Nat.pow_mul]
  rw [e4]; exact h2'

theorem flat_contra [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) {Φ : Nat × Nat → Fin p}
    (hΦ : Flat p K Φ) (h4 : cs p (4 ^ (3 ^ (K - 1))) = 1) : False := by
  have h3 := finv3_mul p hp5
  obtain ⟨a, haK, hk⟩ := order_pow3 p (n := K - 1) h4
  have hk' : ∀ m, cs p (4 ^ m) = 1 ↔ 3 ^ a ∣ m := hk
  have ha1 : 1 ≤ a := by
    apply Classical.byContradiction
    intro h0
    have ha0 : a = 0 := by omega
    subst ha0
    have h1 : cs p (4 ^ 1) = 1 := (hk' 1).2 (by simp)
    rw [Nat.pow_one] at h1
    have h1' : cs p 4 = cs p 1 := by rw [cs_one]; exact h1
    rw [cs_eq_iff, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1'
    omega
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
  obtain ⟨e, he, hΦe⟩ := flat_four_form p hp5 hK hΦ (c := 4 + 9 * r) (by omega) hc2lt
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
  have hm4 := cancel_left_pow hcop4 (Nat.pow_pos (by decide) : 1 ≤ 4 ^ e') hm3
  have hd1 : 3 ^ (a' + 1) ∣ e' :=
    (four_pow_modEq_one_iff (K := a' + 1) (m := e')).1 (by
      rw [hm4, hq2]; exact Nat.mod_eq_of_lt (by omega))
  have hφ2 : Φ (4 + 9 * r, 0) = 4 := by
    rw [hΦe, Nat.pow_succ, cs_mul, (hk' e').2 hd1, cs_four]; grind
  have ub := flat_U p hp5 hΦ (e := 4 + 9 * r) (by omega) (by omega) (by rw [hM2]; omega)
  have tb : (4 + 9 * r - 1) / 3 = 1 + 3 * r := by omega
  have mb1 : (1 + 3 * r) % 3 ^ (K + 1) = 1 + 3 * r := Nat.mod_eq_of_lt (by rw [hM]; omega)
  have mb2 : (4 + 9 * r) % 3 ^ (K + 1) = 4 + 9 * r := Nat.mod_eq_of_lt hc2lt
  rw [tb, mb1, mb2, hφ2] at ub
  have hΦ1 : Φ (1 + 3 * r, 1) = 1 := cancel_unit p h3 (by rw [ub]; grind)
  have hcol := flat_collapse p hp5 hΦ (c := 1 + 3 * r) (by omega) (by rw [hM]; omega)
  have hone : Φ (1 + 3 * r, 0) = 1 := hcol.trans hΦ1
  obtain ⟨d, hd, hΦd⟩ := flat_four_form p hp5 hK hΦ (c := 1 + 3 * r) (by omega) (by rw [hM]; omega)
  have hpd : cs p (4 ^ d) = 1 := hΦd.symm.trans hone
  have hdd : 3 ^ (a' + 1) ∣ d := (hk' d).1 hpd
  have hmodd : 4 ^ d % 3 ^ (a' + 1 + 1) = 1 := (four_pow_modEq_one_iff (K := a' + 1) (m := d)).2 hdd
  have h5 := Nat.mod_mod_of_dvd (4 ^ d) hdv
  rw [hd] at h5
  rw [hq2] at h5 hmodd
  rw [Nat.mod_eq_of_lt (by omega : 1 + 3 * r < 9 * r)] at h5
  omega

theorem no_flat [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) :
    ¬ ∃ Φ : Nat × Nat → Fin p, Flat p K Φ := by
  rintro ⟨Φ, hΦ⟩
  exact flat_contra p hp5 hK hΦ (flat_four_pow p hp5 hK hΦ)

end FlatC

/-! ## Part 9a. Connectivity of the state graph; a common fixed point yields a flat assignment. -/
section Conn
variable (p : Nat) [NeZero p]

theorem walk_two_pow {K : Nat} :
    ∀ j : Nat, ∃ g : Aff p, Walk p K base ((2 ^ j) % 3 ^ (K + 1), 0) g := by
  intro j
  induction j with
  | zero =>
    rw [Nat.pow_zero, Nat.mod_eq_of_lt (one_lt_pow3 K)]
    exact ⟨_, Walk.nil base⟩
  | succ j ih =>
    obtain ⟨g, hg⟩ := ih
    have hc := mod_unit (three_dvd_pow K) (two_pow_mod_three_ne j)
    have hlt := Nat.mod_lt (2 ^ j) (show 0 < 3 ^ (K + 1) by have := one_lt_pow3 K; omega)
    have he := Edge.D (p := p) (K := K) (f := 0) hc hlt (by omega)
    have e : (2 * (2 ^ j % 3 ^ (K + 1))) % 3 ^ (K + 1) = 2 ^ (j + 1) % 3 ^ (K + 1) := by
      have e2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [Nat.mul_mod_mod, e2]
    rw [e] at he
    exact ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil _))⟩

theorem connected_even {K : Nat} {c : Nat} (hc : c % 3 ≠ 0)
    (hlt : c < 3 ^ (K + 1)) : ∃ g : Aff p, Walk p K base (c, 0) g := by
  obtain ⟨j, hj⟩ := two_transitive (K := K) (c := 1) (d := c) (by omega) hc hlt
  rw [Nat.mul_one] at hj
  obtain ⟨g, hg⟩ := walk_two_pow p (K := K) j
  rw [hj] at hg
  exact ⟨g, hg⟩

theorem connected {K : Nat} {c f : Nat}
    (hc : c % 3 ≠ 0) (hlt : c < 3 ^ (K + 1)) (hf : f < 2) :
    ∃ g : Aff p, Walk p K base (c, f) g := by
  have hcase : f = 0 ∨ f = 1 := by omega
  rcases hcase with rfl | rfl
  · exact connected_even p hc hlt
  · have hM : 3 ^ (K + 2) = 3 * 3 ^ (K + 1) := by rw [Nat.pow_succ 3 (K + 1)]; grind
    have h1 : (3 * c + 1) % 3 = 1 := by omega
    have h9 : (3 * c + 1) % 9 ≠ 1 := by omega
    have hlt2 : 3 * c + 1 < 3 ^ (K + 2) := by omega
    have he := Edge.U (p := p) (K := K) (e := 3 * c + 1) h1 h9 hlt2
    have h3c : (3 * c + 1 - 1) / 3 = c := by omega
    rw [h3c, Nat.mod_eq_of_lt hlt] at he
    have hsrc : (3 * c + 1) % 3 ^ (K + 1) % 3 ≠ 0 :=
      mod_unit (three_dvd_pow K) (by omega)
    obtain ⟨g, hg⟩ := connected_even p hsrc
      (Nat.mod_lt _ (by have := one_lt_pow3 K; omega))
    exact ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil _))⟩

open Classical in
theorem flat_of_fixed [PField p] (hp5 : 5 ≤ p) {K : Nat} (x : Fin p)
    (hx : ∀ f, Hol p K f → aapp p f x = x) : ∃ Φ : Nat × Nat → Fin p, Flat p K Φ := by
  have hval : ∀ {u : Nat × Nat} {g1 g2 : Aff p}, Walk p K base u g1 → Walk p K base u g2 →
      aapp p g1 x = aapp p g2 x := by
    intro u g1 g2 h1 h2
    have hh : Hol p K (athen p g1 (ainv p g2)) := Walk.append p h1 (Walk.symm p hp5 h2)
    have hfix := hx _ hh
    rw [athen_app] at hfix
    have hu := Walk.label_unit p hp5 h2
    have hinv : ∀ z, aapp p g2 (aapp p (ainv p g2) z) = z := by
      intro z
      have hi : (ainv p g2).1 ≠ 0 := by
        have h1 := mul_finv' p hu
        intro h0
        simp only [ainv] at h0
        rw [h0] at h1
        exact one_ne_zero_fin p hp5 (by grind)
      have := ainv_app p (ainv p g2) hi z
      rwa [ainv_ainv p g2 hu] at this
    have := congrArg (aapp p g2) hfix
    rw [hinv] at this
    exact this
  refine ⟨fun u => if h : ∃ g, Walk p K base u g then aapp p h.choose x else 0, ?_⟩
  rintro ⟨c, f0⟩ w f he
  obtain ⟨hc, hlt, hf⟩ := Edge.src_valid p he
  obtain ⟨g, hg⟩ := connected p hc hlt hf
  have hu : ∃ g, Walk p K base (c, f0) g := ⟨g, hg⟩
  have hw : ∃ g', Walk p K base w g' :=
    ⟨_, Walk.append p hg (Walk.fwd he (Walk.nil w))⟩
  show (if h : ∃ g, Walk p K base w g then aapp p h.choose x else 0) =
    aapp p f (if h : ∃ g, Walk p K base (c, f0) g then aapp p h.choose x else 0)
  rw [dite_eq_left_of_eq_true (eq_true hw), dite_eq_left_of_eq_true (eq_true hu)]
  have e1 := hval hw.choose_spec (Walk.append p hg (Walk.fwd he (Walk.nil w)))
  have e2 := hval hu.choose_spec hg
  rw [e1, e2, athen_app, athen_app]
  simp only [aapp]; grind

end Conn

/-! ## Part 9b. No common fixed point implies a nonzero translation in the holonomy group. -/
section Trans
variable (p : Nat) [NeZero p]

theorem translation_of_no_fixed [PField p] (hp5 : 5 ≤ p) {K : Nat}
    (hno : ¬ ∃ x : Fin p, ∀ f, Hol p K f → aapp p f x = x) : HasTranslation p K := by
  apply Classical.byContradiction
  intro hnt
  apply hno
  by_cases hall : ∀ f : Aff p, Hol p K f → f.1 = 1
  · refine ⟨0, fun f hf => ?_⟩
    have h1 := hall f hf
    have hz : f.2 = 0 := by
      apply Classical.byContradiction
      intro hne
      apply hnt
      refine ⟨f.2, hne, ?_⟩
      have : f = (1, f.2) := Prod.ext h1 rfl
      rw [← this]; exact hf
    unfold aapp; rw [h1, hz]; grind
  · have hex : ∃ f : Aff p, Hol p K f ∧ f.1 ≠ 1 := by
      apply Classical.byContradiction
      intro h
      apply hall
      intro f hf
      apply Classical.byContradiction
      intro hne
      exact h ⟨f, hf, hne⟩
    obtain ⟨⟨l0, m0⟩, hh0, hl1⟩ := hex
    have hl0 : l0 ≠ 0 := Walk.label_unit p hp5 hh0
    have hl1' : l0 ≠ 1 := hl1
    have hd0 : (1 - l0) ≠ 0 := fun h => hl1' (by grind)
    obtain ⟨id0, hid0⟩ := PField.inv_ex (1 - l0) hd0
    have hi0 := mul_finv' p hl0
    have hx0 : (m0 * id0) * (1 - l0) = m0 := by
      calc (m0 * id0) * (1 - l0) = m0 * ((1 - l0) * id0) := by grind
        _ = m0 := by rw [hid0]; grind
    generalize m0 * id0 = x0 at hx0
    refine ⟨x0, fun k hk => ?_⟩
    obtain ⟨lk, mk⟩ := k
    have hlk : lk ≠ 0 := Walk.label_unit p hp5 hk
    have hil := mul_finv' p hlk
    have hg : Hol p K (athen p (athen p (athen p (lk, mk) (l0, m0)) (ainv p (lk, mk)))
        (ainv p (l0, m0))) :=
      Hol_mul p (Hol_mul p (Hol_mul p hk hh0) (Hol_inv p hp5 hk)) (Hol_inv p hp5 hh0)
    unfold athen ainv at hg
    simp only at hg
    generalize finv p lk = il at *
    generalize finv p l0 = i0 at *
    have h1 : i0 * (il * (l0 * lk)) = 1 := by
      calc i0 * (il * (l0 * lk)) = (l0 * i0) * (lk * il) := by grind
        _ = 1 := by rw [hi0, hil]; grind
    have hm0 : m0 = x0 * (1 - l0) := hx0.symm
    have h2 : i0 * (il * (l0 * mk + m0) + -(il * mk)) + -(i0 * m0)
        = (l0 - 1) * (lk * x0 + mk - x0) * (il * i0) := by
      rw [hm0]
      calc i0 * (il * (l0 * mk + x0 * (1 - l0)) + -(il * mk)) + -(i0 * (x0 * (1 - l0)))
          = (i0 * l0) * (il * mk) + (i0 * il) * (x0 * (1 - l0)) - (i0 * il) * mk - (i0 * (x0 * (1 - l0))) := by grind
        _ = (l0 - 1) * (lk * x0 + mk - x0) * (il * i0) := by grind
    rw [h1, h2] at hg
    by_cases hd : (l0 - 1) * (lk * x0 + mk - x0) * (il * i0) = 0
    · have hA : (l0 - 1) * (lk * x0 + mk - x0) = 0 := by
        calc (l0 - 1) * (lk * x0 + mk - x0)
            = ((l0 - 1) * (lk * x0 + mk - x0) * (il * i0)) * (lk * l0) := by grind
          _ = 0 := by rw [hd]; grind
      have hB : lk * x0 + mk - x0 = 0 :=
        cancel_unit p hid0 (by calc (1 - l0) * (lk * x0 + mk - x0) = -((l0 - 1) * (lk * x0 + mk - x0)) := by grind
                                _ = (1 - l0) * 0 := by rw [hA]; grind)
      unfold aapp; simp only; grind
    · exact absurd ⟨_, hd, hg⟩ hnt

end Trans

/-! ## Part 9c. Simultaneous density modulo a prime, and primality implies the field property. -/
theorem exists_of_card_pos {p : Nat} {S : Fin p → Prop} (h : 1 ≤ card S) : ∃ t, S t := by
  classical
  unfold card at h
  obtain ⟨t, ht⟩ := List.exists_mem_of_length_pos h
  exact ⟨t, (mem_cardlist).1 ht⟩

section Density
variable (p : Nat) [NeZero p]

theorem translation_exists [PField p] (hp5 : 5 ≤ p) {K : Nat} (hK : 1 ≤ K) :
    HasTranslation p K := by
  apply translation_of_no_fixed p hp5
  rintro ⟨x, hx⟩
  obtain ⟨Φ, hΦ⟩ := flat_of_fixed p hp5 x hx
  exact no_flat p hp5 hK ⟨Φ, hΦ⟩

theorem main_theorem_core [PField p] (hp5 : 5 ≤ p) {v : Nat} (hv : v % 2 = 0)
    (hv3 : v % 3 ≠ 0) {J : Nat} (hJ : 1 ≤ J) {c : Nat} (hc : c % 3 ≠ 0)
    (hcl : c < 3 ^ (J + 1)) (r : Fin p) :
    ∃ n, Tree v n ∧ n % 3 ^ (J + 1) = c ∧ cs p n = r := by
  obtain ⟨K0, hK0, hS⟩ := stabilization p hp5 hv hv3
  obtain ⟨K, hKdef⟩ : ∃ K, K = max (max K0 J) 1 := ⟨_, rfl⟩
  have hKK0 : K0 ≤ K := by omega
  have hKJ : J ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  obtain ⟨d, hd0, hd⟩ := translation_exists p hp5 hK1
  have himg := walk_image p hp5 hv hv3 hS hKK0 hK1 hd
  have hpos := sig_pos p hp5 hv hv3 K
  obtain ⟨t0, ht0⟩ := exists_of_card_pos (S := fibre p K v 1 0) hpos
  have step : ∀ t, fibre p K v 1 0 t → fibre p K v 1 0 (t + d) := by
    intro t ht
    have h1 : Img p ((1 : Fin p), d) (fibre p K v 1 0) (t + d) :=
      ⟨t, ht, by unfold aapp; simp only; grind⟩
    exact (himg (t + d)).1 h1
  have key : ∀ k : Nat, fibre p K v 1 0 (t0 + cs p k * d) := by
    intro k
    induction k with
    | zero => rw [cs_zero]; have : t0 + (0 : Fin p) * d = t0 := by grind
              rw [this]; exact ht0
    | succ k ih =>
      have := step _ ih
      have e : t0 + cs p (k + 1) * d = t0 + cs p k * d + d := by
        rw [cs_add, cs_one]; grind
      rw [e]; exact this
  obtain ⟨e, he⟩ := PField.inv_ex d hd0
  have hfull : ∀ r' : Fin p, fibre p K v 1 0 r' := by
    intro r'
    have := key ((r' - t0) * e).val
    have hcs : cs p ((r' - t0) * e).val = (r' - t0) * e := by
      apply Fin.ext
      rw [cs_val, Nat.mod_eq_of_lt (Fin.isLt _)]
    rw [hcs] at this
    have e2 : t0 + (r' - t0) * e * d = r' := by
      calc t0 + (r' - t0) * e * d = t0 + (r' - t0) * (d * e) := by grind
        _ = r' := by rw [he]; grind
    rw [e2] at this; exact this
  have hcK : c < 3 ^ (K + 1) :=
    Nat.lt_of_lt_of_le hcl (Nat.pow_le_pow_right (by decide) (by omega))
  have hfullc : ∀ t, fibre p K v c 0 t := by
    have hcc := fibre_card_const p hp5 (v := v) (K := K) (c := 1) (d := c)
      (by omega) (one_lt_pow3 K) hc hcK
    have hu : card (fibre p K v 1 0) = card (fun _ : Fin p => True) :=
      card_congr (fun t => ⟨fun _ => trivial, fun _ => hfull t⟩)
    have := card_eq_of_sub (S := fibre p K v c 0) (T := fun _ : Fin p => True)
      (fun _ _ => trivial) (by omega)
    exact fun t => this t trivial
  have hr := fibre_proj p hKJ (hfullc r)
  rw [Nat.mod_eq_of_lt hcl] at hr
  obtain ⟨n, hn, hn1, _, hn3⟩ := hr
  exact ⟨n, hn, hn1, hn3⟩

end Density

/-! ## Primes -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

theorem isPrime_pfield {p : Nat} [NeZero p] (hp : IsPrime p) : PField p := by
  refine ⟨fun a ha => ?_⟩
  have hk0 : a.val ≠ 0 := by
    intro h0; apply ha; apply Fin.ext; rw [h0]; rfl
  have hkp : a.val < p := a.isLt
  have hcop : Nat.Coprime p a.val := by
    unfold Nat.Coprime
    rcases hp.2 _ (Nat.gcd_dvd_left p a.val) with h | h
    · exact h
    · exfalso
      have hdv : p ∣ a.val := by
        have := Nat.gcd_dvd_right p a.val
        rwa [h] at this
      have := Nat.eq_zero_of_dvd_of_lt hdv hkp
      exact hk0 this
  have hinj : ∀ s t : Fin p, a * s = a * t → s = t := by
    intro s t h
    have h1 := congrArg Fin.val h
    rw [Fin.val_mul, Fin.val_mul] at h1
    have h2 : (s.val * a.val) % p = (t.val * a.val) % p := by
      rw [Nat.mul_comm s.val, Nat.mul_comm t.val]; exact h1
    have h3 := cancel_right_pow hcop h2
    rw [Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt t.isLt] at h3
    exact Fin.ext h3
  have hc : card (fun _ : Fin p => True) ≤ card (fun t : Fin p => ∃ s, a * s = t) :=
    card_le_of_inj (fun t => a * t) hinj (fun t _ => ⟨t, rfl⟩)
  have := card_eq_of_sub (S := fun t : Fin p => ∃ s, a * s = t) (T := fun _ : Fin p => True)
    (fun _ _ => trivial) hc 1 trivial
  exact this

/-! ## Part 10. Small primes (2 and 3) and the master theorem. -/
section Small

theorem sixtyfour_pow_mod (t : Nat) : 64 ^ t % 9 = 1 := by
  induction t with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem lt_pow_mul {B k w : Nat} (hk : B ≤ k) (hw : 0 < w) : B < 2 ^ k * w := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ 2 ^ k * w := Nat.le_mul_of_pos_right _ hw
  omega

theorem exists_pow_two_mod_one (w : Nat) (hw3 : w % 3 ≠ 0) : ∃ j, j < 6 ∧ 2 ^ j * w % 9 = 1 := by
  have hm9 : w % 9 = 1 ∨ w % 9 = 2 ∨ w % 9 = 4 ∨ w % 9 = 5 ∨ w % 9 = 7 ∨ w % 9 = 8 := by omega
  rcases hm9 with h | h | h | h | h | h
  · exact ⟨0, by omega, by rw [Nat.mul_mod, h]⟩
  · exact ⟨5, by omega, by rw [Nat.mul_mod, h]⟩
  · exact ⟨4, by omega, by rw [Nat.mul_mod, h]⟩
  · exact ⟨1, by omega, by rw [Nat.mul_mod, h]⟩
  · exact ⟨2, by omega, by rw [Nat.mul_mod, h]⟩
  · exact ⟨3, by omega, by rw [Nat.mul_mod, h]⟩

theorem exists_k_mod_three (w t : Nat) (hw3 : w % 3 ≠ 0) :
    ∃ k, 2 * t ≤ k ∧ k ≤ 2 * t + 1 ∧ 2 ^ k * w % 3 = 1 := by
  have h4 := four_pow_mod_three t
  have e : 2 ^ (2 * t) = 4 ^ t := by rw [Nat.pow_mul]
  have hcase : w % 3 = 1 ∨ w % 3 = 2 := by omega
  rcases hcase with h | h
  · refine ⟨2 * t, Nat.le_refl _, by omega, ?_⟩
    rw [e, Nat.mul_mod, h4, h]
  · refine ⟨2 * t + 1, by omega, Nat.le_refl _, ?_⟩
    have e3 : 2 ^ (2 * t + 1) * w = 4 ^ t * (2 * w) := by
      rw [Nat.pow_succ, e]; grind
    rw [e3, Nat.mul_mod, h4]
    omega

theorem odd_of_three_mul_add_one {w k q : Nat} (hk : 1 ≤ k)
    (hq : 3 * q + 1 = 2 ^ k * w) : q % 2 = 1 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 ^ (k' + 1) * w = 2 * (2 ^ k' * w) := by rw [Nat.pow_succ]; grind
  omega

theorem reaches_of_three_mul_add_one {w k q : Nat} (hk : 1 ≤ k)
    (hq : 3 * q + 1 = 2 ^ k * w) : Reaches w q := by
  have hodd := odd_of_three_mul_add_one hk hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hc : collatz q = 2 ^ (k' + 1) * w := by
    unfold collatz
    split
    · omega
    · exact hq
  refine ⟨k' + 1 + 1, ?_⟩
  show iter collatz (k' + 1) (collatz q) = w
  rw [hc]
  exact collatz_pow_mul _ _

theorem exists_large_unit_class (B : Nat) :
    ∃ J c : Nat, 1 ≤ J ∧ c % 3 ≠ 0 ∧ c < 3 ^ (J + 1) ∧ B < c := by
  have hpos : 0 < 3 ^ B := Nat.pow_pos (by decide)
  refine ⟨B + 1, 9 * 3 ^ B - 1, by omega, by omega, ?_, ?_⟩
  · have : 3 ^ (B + 1 + 1) = 9 * 3 ^ B := by rw [Nat.pow_succ, Nat.pow_succ]; grind
    rw [this]; omega
  · have hB : B < 3 ^ B := Nat.lt_pow_self (by decide)
    omega

end Small

section Final
variable (p : Nat) [NeZero p]

theorem main_theorem_p_ge_5 [PField p] (hp5 : 5 ≤ p) (w : Nat) (hw3 : w % 3 ≠ 0)
    (r B : Nat) : ∃ n : Nat, B < n ∧ Reaches w n ∧ n % p = r % p := by
  obtain ⟨J, c, hJ, hc, hcl, hBc⟩ := exists_large_unit_class B
  have hv : (2 * w) % 2 = 0 := by omega
  have hv3 : (2 * w) % 3 ≠ 0 := by omega
  obtain ⟨n, hn, hnc, hnr⟩ := main_theorem_core p hp5 hv hv3 hJ hc hcl (cs p r)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hnc; omega
    · exact h
  have hcn : c ≤ n := by rw [← hnc]; exact Nat.mod_le _ _
  have hsw : Reaches w (2 * w) := ⟨1, by simp [iter, collatz_double]⟩
  exact ⟨n, by omega, reaches_trans (Tree_reaches hn) hsw, (cs_eq_iff p n r).1 hnr⟩

end Final

theorem main_theorem_p_eq_2 (w : Nat) (hw : 0 < w) (hw3 : w % 3 ≠ 0) (r B : Nat) :
    ∃ n : Nat, B < n ∧ Reaches w n ∧ n % 2 = r % 2 := by
  have hcase : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hcase with h | h
  · refine ⟨2 ^ (B + 1) * w, lt_pow_mul (by omega) hw,
      ⟨B + 1, collatz_pow_mul _ _⟩, ?_⟩
    have e : 2 ^ (B + 1) * w = 2 * (2 ^ B * w) := by rw [Nat.pow_succ]; grind
    rw [e]; omega
  · obtain ⟨k, hk1, _hk2, _hk3⟩ := exists_k_mod_three w (3 * B + 3) hw3
    have hbig := lt_pow_mul (B := 6 * B + 6) (k := k) (w := w) (by omega) hw
    have hq : 3 * (2 ^ k * w / 3) + 1 = 2 ^ k * w := by omega
    refine ⟨2 ^ k * w / 3, by omega, reaches_of_three_mul_add_one (by omega) hq, ?_⟩
    have := odd_of_three_mul_add_one (by omega : 1 ≤ k) hq
    omega

theorem main_theorem_p_eq_3 (w : Nat) (hw : 0 < w) (hw3 : w % 3 ≠ 0) (r B : Nat) :
    ∃ n : Nat, B < n ∧ Reaches w n ∧ n % 3 = r % 3 := by
  have hcase : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hcase with h | h | h
  · obtain ⟨j, _, hj⟩ := exists_pow_two_mod_one w hw3
    have h64 : (2 : Nat) ^ (6 * (B + 1)) = 64 ^ (B + 1) := by rw [Nat.pow_mul]
    have e : 2 ^ (j + 6 * (B + 1)) * w = 64 ^ (B + 1) * (2 ^ j * w) := by
      rw [Nat.pow_add, h64]; grind
    have hm := Nat.mul_mod (64 ^ (B + 1)) (2 ^ j * w) 9
    rw [sixtyfour_pow_mod (B + 1), hj] at hm
    have hN : 2 ^ (j + 6 * (B + 1)) * w % 9 = 1 := by rw [e]; omega
    have hq : 3 * (2 ^ (j + 6 * (B + 1)) * w / 3) + 1 = 2 ^ (j + 6 * (B + 1)) * w := by omega
    have hbig := lt_pow_mul (B := 6 * B + 6) (k := j + 6 * (B + 1)) (w := w) (by omega) hw
    exact ⟨2 ^ (j + 6 * (B + 1)) * w / 3, by omega,
      reaches_of_three_mul_add_one (by omega) hq, by omega⟩
  · obtain ⟨k, _hk1, _hk2, _hk3⟩ := exists_k_mod_three w B hw3
    exact ⟨2 ^ k * w, lt_pow_mul (by omega) hw, ⟨k, collatz_pow_mul _ _⟩, by omega⟩
  · obtain ⟨k, _hk1, _hk2, _hk3⟩ := exists_k_mod_three w B hw3
    refine ⟨2 ^ (k + 1) * w, lt_pow_mul (by omega) hw, ⟨k + 1, collatz_pow_mul _ _⟩, ?_⟩
    have e : 2 ^ (k + 1) * w = 2 * (2 ^ k * w) := by rw [Nat.pow_succ]; grind
    rw [e]; omega

/-- **Every Remainder Everywhere (atomic form).** For every prime `p`, every `w > 0` not divisible
by `3`, every residue `r` and every bound `B`, some `n > B` reaches `w` under the Collatz map and
satisfies `n ≡ r (mod p)`. -/
theorem main_theorem (p : Nat) (hp : IsPrime p) (w : Nat) (hw : 0 < w) (hw3 : w % 3 ≠ 0)
    (r B : Nat) : ∃ n : Nat, B < n ∧ Reaches w n ∧ n % p = r % p := by
  have h2 := hp.1
  haveI : NeZero p := ⟨by omega⟩
  by_cases hp5 : 5 ≤ p
  · haveI := isPrime_pfield hp
    exact main_theorem_p_ge_5 p hp5 w hw3 r B
  · have hp23 : p = 2 ∨ p = 3 := by
      have h4 : p ≠ 4 := by
        intro h
        have := hp.2 2 (by rw [h]; decide)
        omega
      omega
    rcases hp23 with rfl | rfl
    · exact main_theorem_p_eq_2 w hw hw3 r B
    · exact main_theorem_p_eq_3 w hw hw3 r B

/-! ## Sanity checks (the definitions behave as intended) -/

example : collatz 7 = 22 := by decide
example : Reaches 1 6 := ⟨8, by decide⟩

theorem isPrime_seven : IsPrime 7 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle : d ≤ 7 := Nat.le_of_dvd (by decide) hd
  have : ∀ d, d ≤ 7 → d ∣ 7 → d = 1 ∨ d = 7 := by decide
  exact this d hle hd

example : ∃ n, 100 < n ∧ Reaches 1 n ∧ n % 7 = 3 := by
  have := main_theorem 7 isPrime_seven 1 (by decide) (by decide) 3 100
  simpa using this

end AtomicERE

#print axioms AtomicERE.main_theorem
