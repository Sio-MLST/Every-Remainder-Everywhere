# Dossier: left-branch disjunctiveness, BBP, and digit-to-word bridges

Status tags: **\[proved\]** = short proof given or standard. **\[derived\]** = derived here and checked numerically, proof needs one more pass. **\[numeric\]** = observed in computation only. **\[idea\]** = tentative. **\[open\]** = unresolved.

Note: these statuses were assigned by an LLM and are **\[dubious\]** by default unless externally verified. **\[proved\]** means a short argument is written out next to the claim, not that it has been independently checked.

Scope: three threads. (1) The left branch alone. (2) BBP, treated as a second instance of the specific-number problem (π is the motivating example only). (3) Digit-level versus word-level disjunctiveness, and what is still missing for normality. Every Remainder Everywhere (ERE) is used as a black box.

**Revision notes.** Derivations sit next to each result, in blocks headed *Derivation*. Corrections: 1.2 and 1.4 (disjunctive in base b does imply full support in every b^k, so digit-level and word-level disjunctiveness over base powers are equivalent); Theorem B's seeds now lie in the valid classes; summary item 4 now names the commutator the argument actually uses. New: 1.8 (hot-spot criterion), 2.8 (quantifiers), 2.9 (dyadic versus triadic), an appendix with the scripts, and a citation pass (abstracts and secondary sources read, not the full papers). Section 3 is reframed: π is a motivating example of the specific-number problem, not a target.

**Second and third revisions (pure-Lean port, composite moduli).** Section 2.10 records what porting the atomic ERE proof to pure Lean (no Mathlib) established. Section 2.11 is a self-contained handover of the open problem for composite moduli, so that a new assistant given AtomicERE\_pure.lean and this dossier can continue. Appendix E and F add the scripts. Tags: **\[checked in Lean\]** means the statement compiled in AtomicERE\_pure.lean (Lean 4.36.0-rc1, standard axioms only, `leanchecker` passes); everything else keeps the tags above. No earlier claim in this dossier needed correcting.

## 0. Summary

1. **Cofinal Wall \[proved\].** Simple normality in base b^k for *infinitely many* k already gives normality in base b. Likewise, full alphabet support in base b^k for infinitely many k gives disjunctiveness. "All k" is not needed.
2. **The left branch cannot be word-disjunctive if you read consecutive orbit residues as digits \[proved\].** From a residue t only a few next residues are possible. The fix is to sample the orbit sparsely.
3. **The left branch is a Markov-modulated random affine walk, not an i.i.d. one \[derived, checked\].** This corrects my earlier claim in this chat. The run-length marginals are (2/9, 4/9, 1/9, 2/9) for μ = 2, 4, 8, 16, but consecutive runs are dependent.
4. **ERE becomes explicit rational translations \[derived\].** In the left branch the loop group at class A contains f\_4 and f\_16, whose commutator is the translation by −9/32 (2.4). The full group Γ also contains \[f\_2, f\_4\] = −3/8. Both are unit translations modulo every M coprime to 6, which gives irreducibility for all such moduli at once, including prime powers.
5. **Two theorems follow \[derived\].** (A) For 3-adically generic seeds, sparse sampling gives almost-sure disjunctiveness (constant gap) or normality (growing gaps). (B) A Champernowne-style concatenation over the left orbits of *all* seeds is provably normal in every base b coprime to 6.
6. **Single seed 8 \[open\].** It reduces to a ×2 / ×3 digit-interaction problem (Furstenberg flavor). ERE does not reach it, because ERE quantifies over all branch choices.
7. **BBP and π: a second specific-number problem \[open\].** Normality of π and normality of a single left-only orbit are the same kind of problem: showing that one specific deterministic sequence is generic. Almost-every results and averaged constructions do not decide a particular number. Corrected fact: the Bailey–Crandall perturbation r\_n is O(n⁻²), not O(1/n). Section 3 records what BBP does and does not give.

## 1. Digits versus words

Let x be irrational, b ≥ 2. Write the base-b expansion as (d\_n). A base-b^k digit is an *aligned* block of k base-b digits.

**Definitions.**

- FS(b): every symbol of {0..b−1} occurs.
- Disj(b): every finite word occurs.
- Ladder(b): FS(b^k) holds for every k ≥ 1.

**1.1 Ladder ⇒ disjunctive \[proved\].** A word w of length k is one base-b^k digit. If that digit occurs, w occurs aligned. Moreover, a *cofinal* set of k suffices: a word of length m ≤ k is a prefix of some k-word. So FS(b^k) for infinitely many k already gives Disj(b).

**1.2 Disjunctive ⇒ full support in every b^k (the converse of 1.1) \[proved\].** Let v be a b^k-digit, i.e. a base-b word of length k. Form W = v z v z … z v, with k copies of v and one arbitrary symbol z between neighbours. If W occurs starting at position j, the copies of v start at j + m(k+1) for m = 0, …, k−1. Modulo k these are j + m, so every residue class occurs and one copy starts at a position ≡ 1 (mod k), i.e. is aligned. Hence Disj(b) ⇒ FS(b^k) for every k. Applying the same argument to words of length jm gives Disj(b) ⇒ Disj(b^j). With 1.1: Disj(b) ⇔ FS(b^k) for all k ⇔ FS(b^k) for infinitely many k ⇔ Disj(b^j) for all j. If x has FS(B) for every integer base B ≥ 2, it is disjunctive in every base.

**1.3 Irrationality is automatic \[proved\].** A rational x has an eventually periodic expansion in every base, hence only finitely many distinct b^k-digits, which is fewer than b^k for large k. So FS(b^k) for infinitely many k forces x irrational.

*Derivation.* A rational x has an eventually periodic base-b expansion, say preperiod N0 and period P. Regrouping into blocks of k digits keeps it eventually periodic, so at most N0 + P distinct blocks occur. Once b^k > N0 + P, some b^k-digit is missing.

**1.4 What this does to the "Ladder" idea \[derived, corrects an earlier draft\].** An earlier version claimed Disj(b) does not imply FS(b^k). That is false by 1.2. So "digit-disjunctive in every b^k" and "word-disjunctive" are the same property, and the step from digits to words costs one short counting argument, not a research problem. The real gap is only disjunctive → normal (see 1.6 and 1.7). One caution: FS(b^k) for a *single* k (say every hex digit appears) is much weaker than Disj(b); it is the family over k that carries the strength.

**1.5 Orbit formulation \[proved\].** Word w of length k occurs at position n+1 iff {b^n x} ∈ \[w/b^k, (w+1)/b^k). So:

*Derivation.* If x = Σ d\_i b^{−i}, then b^n x mod 1 = Σ\_{i≥1} d\_{n+i} b^{−i} = 0.d\_{n+1}d\_{n+2}…. This lies in \[w/b^k, (w+1)/b^k) exactly when d\_{n+1}…d\_{n+k} spells w (w read as an integer in base b). So "word w occurs" means "the ×b orbit enters the interval of w".

- Disj(b) ⇔ the ×b orbit of x is dense mod 1.
- FS(b^k) ⇔ the sparse orbit {b^{kn} x}\_n meets every level-k interval.
- Normal(b) ⇔ the ×b orbit is equidistributed.

Ladder is therefore a sparse-orbit hitting condition at every scale.

**1.6 Cofinal Wall \[proved\].** *If x is simply normal in base b^k for infinitely many k, then x is Borel normal in base b.*

Proof. Fix a word w of length m. Take k ≥ m with x simply normal in b^k. For an offset j ∈ {0, …, k−m}, the positions ≡ j+1 (mod k) where w occurs inside an aligned block correspond to b^{k−m} out of b^k digit values, so their frequency is b^{−m}. The remaining m−1 offsets straddle blocks. Their total contribution to the frequency is at most (m−1)/k. So the frequency of w lies in \[b^{−m}(1 − (m−1)/k), b^{−m} + (m−1)/k\]. Let k → ∞ along the infinite set. ∎

(The classical Niven–Zuckerman / Wall criterion says "all k". The proof only ever uses unbounded k.)

**1.7 What disjunctive → normal really needs \[idea, but the right frame\].**

- No deterministic implication exists. Disjunctive is about *support*; normal is about *measure*.
- The bridge that does work: a Markov-driven sequence on a finite state space whose reachability graph is strongly connected and aperiodic. Perron–Frobenius then gives a unique stationary law and exponential mixing. Reachability becomes spectral gap.
- So the honest statement is: *irreducible + aperiodic + the driver is generic for the chain ⇒ normal.* The only extra input beyond reachability is genericity of the driver.
- This is the exact upgrade of ERE's "fibre = all of Z/p".

**1.8 The hot-spot criterion: one-sided control is enough \[citations checked at abstract level, derivation sketched\].**

*Weak hot-spot theorem* (Kuipers–Niederreiter, as cited in Bailey's note): α is b-normal iff there is a constant C with limsup\_n (1/n)·#{j < n : {b^j α} ∈ \[c, d)} ≤ C(d − c) for every interval \[c, d). Bailey and Misiurewicz (Proc. AMS 134 (2006) 2495–2501) strengthen this: α is b-normal iff no point y is a hot spot, i.e. visited with frequency exceeding the neighbourhood length by arbitrarily large factors.

*Derivation of the easy direction.* If α is normal, the visit frequency of \[c, d) tends to d − c, so C = 1 works. The converse is the theorem; I have not reproduced its proof.

*Why it matters here.* Passing from "every word occurs" to "every word occurs at the right rate" needs only an upper bound of order |I| on how often any interval is visited. Bounds of this kind are what counting and exponential-sum arguments produce; Bailey–Crandall used the weak form for explicit lacunary constants such as Σ 1/(3^k·2^{3^k}). For the left branch it suggests a sharper target: for the real number whose digits are the sparse residues, prove limsup visit-frequency ≤ C|I|, instead of proving equidistribution outright.

## 2. The left branch alone

### 2.1 The map

Atomic tree: D: n ↦ 2n; U: n ↦ (n−1)/3, allowed when n ≡ 4 (mod 6) and the result is live (3 ∤ it), which means n ≢ 1 (mod 9).

**Greedy-U (left branch) map \[proved\].** G(n) = (n−1)/3 if n mod 18 ∈ {4, 16}, otherwise G(n) = 2n.

Orbit of 16: 16, 5, 10, 20, 40, 13, 26, 52, 17, 34, 11, 22, 7, 14, 28, 56, 112, 37, …

Subsampled at the U-steps, this is exactly your T(x) = μ(x)(2x−1)/6 in x-coordinates, with μ/2 = 2^i. One *T-step* means one U together with the doublings around it. Each T-step consumes exactly one 3-adic digit.

Closed form \[proved\]: after d doublings and u undos, n = (2^d n\_0 − C\_w)/3^u with C\_w an integer depending on the word w.

*Derivation (greedy = T).* Take a valid x (x ≡ 2 or 8 mod 9). Then 2x is even with 2x ≡ 4 or 7 mod 9, so 2x mod 18 ∈ {4, 16} and the greedy rule fires U at 2x: m = (2x−1)/3, which is odd because 3m = 2x−1 is odd. An odd node is never ≡ 4 mod 6, so the rule doubles next, and keeps doubling until y = 2^i m has 2y mod 18 ∈ {4, 16}, i.e. y ≡ 2 or 8 mod 9 (valid again). So the next valid point is y = 2^i (2x−1)/3 = μ(2x−1)/6 with μ = 2^{i+1}. Since 2 generates the units mod 9 and m is a unit, i ≤ 3 and μ ∈ {2, 4, 8, 16}.

*Derivation (closed form).* Write n = (2^d n\_0 − C)/3^u. A D-step gives (2^{d+1} n\_0 − 2C)/3^u, so d → d+1 and C → 2C. A U-step gives (n−1)/3 = (2^d n\_0 − C − 3^u)/3^{u+1}, so u → u+1 and C → C + 3^u. By induction C is an integer, which also shows each U-step is an exact division.

### 2.2 Obstruction to consecutive digits \[proved\]

From residue t mod p the next T-step residue is f\_μ(t) = μ(2t−1)/6 with μ ∈ {2, 4, 8, 16}. So at most 4 successors, and 4p < p² for p ≥ 5. For G-steps it is at most 2 successors.

Therefore α\_p, defined with consecutive orbit residues as digits, misses at least p² − 4p two-blocks. It is not word-disjunctive in base p, for any seed. Digit equidistribution can still hold.

Repair: define digits by sampling every g-th T-step (gaps g\_j possibly growing).

### 2.3 The law of the pattern \[derived, checked\]

Work with even states (x, flag). U triggers at an even state iff x mod 9 ∈ {4, 7}. D multiplies by 2, which cycles the unit classes mod 9 in the order 1 → 2 → 4 → 8 → 7 → 5 → 1.

After a U from class c, x' = (x−1)/3 has x' ≡ (c−1)/3 (mod 3). Its lift mod 9 is uniform among 3 values, **for 3-adically generic seeds and for complete residue systems of seeds** (the next 3-adic digit enters bijectively and the past depends only on lower digits). Table, with c = 4 called A and c = 7 called B:

| from | start class after first D | D-run L (μ = 2^L) | next U-class |
| --- | --- | --- | --- |
| A (c=4) | 2 | 2 (μ=4) | 4 (A) |
| A | 8 | 2 (μ=4) | 7 (B) |
| A | 5 | 4 (μ=16) | 4 (A) |
| B (c=7) | 4 | 1 (μ=2) | 4 (A) |
| B | 1 | 3 (μ=8) | 4 (A) |
| B | 7 | 1 (μ=2) | 7 (B) |

Each row has probability 1/3 given its source. Consequences:

- Next-class law is (A, B) = (2/3, 1/3) from either source, so the classes are i.i.d.
- Marginal law of μ: P(2) = 2/9, P(4) = 4/9, P(8) = 1/9, P(16) = 2/9. Mean number of doublings per U is 7/3. Growth per T-step is (7/3)ln 2 − ln 3 ≈ 0.519.
- The μ-sequence is **not** i.i.d.: a run of length 3 or 4 is always followed by a run of length 2 or 4.

Checks \[numeric\]:

- Orbit of 16, 60,000 G-steps: run law (0.220, 0.449, 0.110, 0.221), mean D per U 2.331, growth 0.5176. Residues mod 5, 7, 11 are flat.
- Complete system of 3^11 seeds, first 8 U-steps: marginals exactly (2/9, 4/9, 1/9, 2/9). The joint pair frequencies show zeros at (3,1), (3,3), (4,1), (4,3), as the table predicts.

So the correct model is a **Markov-modulated random affine walk** on Z/M with a hidden class in {A, B}.

*Derivation of the table.*

1. **Trigger.** U fires at an even x iff x ≡ 4 mod 6 and x ≢ 1 mod 9. For even x with x ≡ 1 mod 3 this means x mod 9 ∈ {4, 7}.
2. **Class after U.** If x ≡ c mod 9 then x mod 27 ∈ {c, c+9, c+18}, so x' = (x−1)/3 ≡ (c−1)/3 + 3s mod 9 with s ∈ {0,1,2}. c = 4 gives x' ∈ {1, 4, 7} (type A). c = 7 gives x' ∈ {2, 5, 8} (type B).
3. **Why s is uniform.** x = (2^d x\_0 − C)/3^u, so x mod 9 depends only on (2^d x\_0 − C) mod 3^{u+2}, i.e. on digits ≤ u+1 of x\_0. The digit s sits at position u+2 and enters through multiplication by the unit 2^d plus a known term, so it is uniform and independent of everything already used.
4. **Waiting time.** After U comes one forced D (x' is odd), landing in class 2x' mod 9. Further D's multiply by 2, which walks the cycle 1→2→4→8→7→5→1; we stop at class 4 or 7. From A: 2x' ∈ {2, 8, 5}; 2→4 needs 1 more D, 8→7 needs 1, 5→1→2→4 needs 3. From B: 2x' ∈ {4, 1, 7}; 0, 2 (1→2→4), 0 more. So L = 1 + extra.
5. **Marginals.** The next U-class is 7 (type B) in one of three rows from either source, so P(B next) = 1/3. Then P(L=1) = P(source B)·(2/3) = 2/9, P(L=2) = P(source A)·(2/3) = 4/9, P(L=3) = (1/3)(1/3) = 1/9, P(L=4) = (2/3)(1/3) = 2/9. E\[L\] = (2+8+3+8)/9 = 7/3. A T-step multiplies x by about μ/3, so growth per T-step is E\[ln μ\] − ln 3 = (7/3) ln 2 − ln 3 ≈ 0.519.
6. **Dependence.** L ∈ {3, 4} ends at class 4, so the next source is A and the next L ∈ {2, 4}. That is exactly the zero pattern seen in the all-seeds computation.

Checked: steps 1–5 against the orbit of 16 and the 3^11-seed computation (numeric). Step 3 is an argument, not a computation.

### 2.4 Irreducibility modulo every M coprime to 6 \[derived\]

Let f\_μ(t) = (μ/3)t − μ/6. Fixed points: μ = 2: −1; μ = 4: 2; μ = 8: 4/5; μ = 16: 8/13. They are distinct.

Commutators computed in Aff(Q):

- &#91;f\_2, f\_4\] = translation by −3/8.
- &#91;f\_4, f\_16\] = translation by −9/32.
- &#91;f\_8, f\_16\] = translation by −3/32. (Other pairs give multiples of these.)

The loop group at class A (words that return to A) contains f\_4 and f\_16, hence the translation by −9/32. For every M coprime to 6 this is a unit translation, so the loop group is transitive on Z/M. The chain on (class, residue) is irreducible. It is aperiodic because f\_2 has a fixed point (slope 2/3 ≠ 1 modulo any such M).

*Derivation (fixed points).* f\_μ(t) = (μ/3)t − μ/6 = t ⇒ t(μ−3)/3 = μ/6 ⇒ t\* = μ/(2(μ−3)). So μ = 2 → −1, μ = 4 → 2, μ = 8 → 4/5, μ = 16 → 8/13.

*Derivation (the commutator).* Compose affine maps by f;g = (s\_g s\_f, s\_g b\_f + b\_g). Take f = f\_2 = (2/3, −1/3) and g = f\_4 = (4/3, −2/3). Then f;g = (8/9, −10/9). Also f⁻¹ = (3/2, 1/2) and g⁻¹ = (3/4, 1/2). So (f;g);f⁻¹ = (4/3, −7/6), and then ;g⁻¹ = (1, −7/8 + 1/2) = (1, −3/8). Slope 1 means a translation, here by −3/8. The same four compositions for f\_4 and f\_16 give −9/32. Both were also checked with exact fractions in code.

*Derivation (transition matrix).* States are (c, t) with c ∈ {A, B}, t ∈ Z/M. Each row of the table, "source c, map μ, next class c'", adds 1/3 to the entry from (c, t) to (c', f\_μ(t)), for every t. From A the three rows are (μ=4, A), (μ=4, B), (μ=16, A). From B they are (μ=2, A), (μ=8, A), (μ=2, B). Every f\_μ is a bijection of Z/M when M is coprime to 6 (slope μ/3 is a unit), so each row is a permutation matrix on t, and the uniform law on t (times any class law) is stationary.

*Derivation (irreducible, aperiodic).* A→A is possible by f\_4 and by f\_16, so the loop group at A contains both, hence their commutator, the translation by −9/32. For M coprime to 6, 9/32 is a unit mod M, so its multiples fill Z/M: from (A, t) one reaches (A, r) for every r. The rows A→B (μ=4) and B→A (μ=2, 8) connect the two classes. For aperiodicity, the row B→B has map f\_2 with fixed point −1, giving a self-loop at (B, −1).

**Observation.** The full rational group Γ = ⟨f\_2, f\_4, f\_8, f\_16⟩ ⊂ Aff(Q) has translation subgroup containing Z\[1/6\]. That is a clean "every remainder everywhere" statement for the left branch. It is stronger than a statement about primes, and the proof is just a commutator.

*Derivation.* For an affine map f(t) = st + b, conjugating a translation T\_τ gives f∘T\_τ∘f⁻¹ = T\_{sτ}. The slopes available in Γ are μ/3 ∈ {2/3, 4/3, 8/3, 16/3} and their inverses; 2 = (4/3)/(2/3) and 3 = 2/(2/3), so products of slopes give every 2^a·3^b. The translations in Γ are closed under addition and under multiplication by these slopes, so they form a Z\[1/6\]-module. It contains 3/8 (from \[f\_2, f\_4\]), which is a unit of Z\[1/6\]; hence it contains all of Z\[1/6\].

Note: p = 5 makes f\_8 a pure translation, and p = 13 does the same for f\_16. This is harmless.

Numerics for the corrected chain on 2p states \[numeric\]:

| p | covering length g\_cov (T-steps) | \|λ₂\| |
| --- | --- | --- |
| 5 | 4 | 0.51 |
| 7 | 4 | 0.67 |
| 11 | 5 | 0.59 |
| 13 | 6 | 0.59 |
| 17 | 6 | 0.57 |
| 31 | 7 | 0.70 |
| 61 | 7 | 0.61 |
| 101 | 8 | 0.65 |
| 127 | 8 | 0.50 |
| 251 | 9 | 0.56 |

(g\_cov = least g with every entry of the g-step support matrix positive.) The growth is consistent with g\_cov ≈ C log p, and |λ₂| stays below about 0.7 in this sample. **\[open\]** Conjecture: g\_cov(p) ≤ C log p and |λ₂| ≤ 0.8 uniformly in p. This is an expander-type question for the affine group generated by x ↦ 2x and x ↦ 3x+1 (inverse direction). Sum–product / Bourgain-type results on random walks in Aff(F\_p) are the literature to check.

*Caution.* g\_cov is the number of steps after which every residue is *possible* from every state. Actually *seeing* every residue along a single orbit is a coupon-collector event and takes about p·log p steps (Researcher's Bible, 9.5; not re-derived here). Do not read g\_cov ≈ C log p as a covering time.

### 2.5 Two theorems

Let b be coprime to 6, digits = residues mod b.

**Theorem A (generic seeds) \[derived\].** For Haar-almost every 3-adic seed ξ and every starting residue r: (a) the sparse residue sequence y\_j = x\_{t\_j} mod b with *constant* gap g ≥ g\_cov(b) has every finite word occurring with positive frequency. So it is almost surely disjunctive. (b) With gaps g\_j → ∞ the sequence is almost surely normal in base b. (c) With bounded gaps it is not normal: the k-block law is the Markov stationary law, not uniform.

Sketch. Under genericity the maps form the Markov-modulated chain above. Each map is a bijection of Z/b, so uniform is stationary for the residue coordinate. Irreducible plus aperiodic gives exponential convergence. In (a), P^g has all entries positive, so every k-word has positive stationary probability. In (b), conditional on the past the transition kernel is P^{g\_j} → uniform in total variation, and variance bounds give a.s. frequencies. ∎

*Derivation of (a) and (c) \[sketch\].* The chain on (class, residue) is finite, irreducible and aperiodic (2.4). The ergodic theorem for finite chains gives, from any start, that each state pattern has a limiting frequency equal to its stationary probability. With constant gap g the observed residues come from P^g. If P^g has all entries positive, every residue word has positive probability, so every word has positive frequency. With bounded gaps the stationary k-block law is π(y\_1) P^g(y\_1, y\_2) …, which is not uniform unless P^g is, so normality fails.

*Derivation of (b) \[sketch\].* Let X\_j = 1\[w starts at sample j\]. Given the past, y\_{j+1} has law P^{g\_j}(·), within total variation Cρ^{g\_j} of uniform, so E\[X\_j\] → b^{−k} and Cov(X\_i, X\_j) = O(ρ^g) for |i−j| > k. Hence Var(Σ\_{j≤N} X\_j) = O(N); Chebyshev plus Borel–Cantelli along N = m² give almost-sure convergence to b^{−k}, and monotonicity fills in the other N. The variance bound with growing gaps is the part still to be written carefully.

**Theorem B (all seeds, Champernowne-style) \[derived\].** Define Λ\_b as the base-b number whose digits are the concatenation, over L = 1, 2, 3, …, over every seed x\_0 in the valid classes (x\_0 ≡ 2 or 8 mod 9) of a complete residue system mod 3^L·b, of the sparse T-step residues (x\_{g\_L·j} mod b), j < J\_L ≈ L−3, with g\_L → ∞ slowly. Then Λ\_b is normal in base b.

Sketch. Fix L. By CRT, (3-adic class of the seed, seed mod b) ranges uniformly over the product. Each T-step eats exactly one 3-adic digit, so the first L−3 T-steps are an *exact* finite cylinder of the Markov-modulated law, with no probabilistic tail. The residue coordinate is uniform and independent of the pattern. The empirical k-word law inside a phase is therefore exactly the chain's sparse k-block law, which is p^{−k}(1 + O(ρ^{g\_L})). Words straddling seed or phase boundaries have relative frequency O(k/J\_L) → 0. ∎

*Derivation of the exactness \[sketch\].* After k T-steps u = k undo-steps have occurred, so the first k steps depend only on x\_0 mod 3^{k+2}. At each U the next 3-adic digit of the running number is uniform over a complete residue system mod 3^L (L ≥ k+2): the residues split into three equal parts by that digit, and this repeats by induction. So each length-k pattern occurs with exactly the probability the Markov-modulated chain assigns it. By CRT, x\_0 mod b is independent of x\_0 mod 3^L, and x\_k mod b = F\_pattern(x\_0 mod b) with F an affine bijection, so x\_k mod b is exactly uniform and (pattern, residue) is exactly the chain started from (initial class law) × uniform. Inside one seed-phase, the frequency of a sparse k-word is therefore Σ over residue paths of b^{−1} Π P^g(·,·) = b^{−k}(1 + O(ρ^g)). The pattern marginals over all 3^11 seeds came out exactly (2/9, 4/9, 1/9, 2/9) (numeric check).

Status. Theorem B is a genuine theorem in the Champernowne / Davenport–Erdős tradition. It does not need ERE in full: it uses the left branch plus the commutator translation. It is not a statement about one natural orbit.

### 2.6 The single seed (the 8-orbit) \[open\]

- The 3-adic coordinate of the integer orbit is the orbit of the 3-adic point 8 under the 3-adic extension of G. The consumed digits are the low digits of (2^d·8 − C\_w)/3^u, which behave like *middle digits of powers of 2 in base 3*.
- So "left branch, one orbit, equidistributed pattern" is a ×2 / ×3 digit-interaction problem. Unconditional results are weak. Stewart (J. reine angew. Math. 319 (1980) 63–72), as quoted in secondary sources, shows the number of nonzero ternary digits of 2^m exceeds log m/(log log m + c) − 3 for m ≥ 25; Senge–Straus (1971) gave the qualitative version. Lagarias (Exp. Math. 10 (2001) 355–368) notes the analogy between Bailey–Crandall's Hypothesis A and Furstenberg's conjecture. These citations were checked at abstract or secondary-source level only.
- ERE says all branch choices together fill everything. A single deterministic orbit is a separate statement. The empirical agreement of the 8-orbit with the generic law is strong evidence, not a proof.

**The cell chain is a model, not a quotient \[derived by hand, example from the Researcher's Bible\].** 8 and 35 are both ≡ 8 mod 27 with μ = 8, but T(8) = 8·15/6 = 20 and T(35) = 8·69/6 = 92 ≡ 11 mod 27. So the next cell depends on a digit the state does not carry (a state mod 3^m remembers about m−1 steps). The chain describes generic seeds only; it says nothing about the orbit of 8 itself.

### 2.7 Ideas for the left branch \[idea\]

1. **Explicit generic seeds.** Build a seed whose digits are provably generic for the skew product, in the style of polynomial-time absolutely normal number constructions (Becher–Heiber–Slaman, Inf. Comput. 232 (2013) 1–9; Lutz–Mayordomo, arXiv:1611.05911). That would give an explicit 3-adic seed ξ with α\_b normal by Theorem A. Honest status: it is a construction, not a natural constant, and adapting those papers from digit-normality to genericity for a skew product is not checked.
2. **Average over seeds, then derandomize.** Theorem B is the averaged object. Ask for the smallest family of seeds (e.g. seeds of the form 2^N·8, or seeds in a single arithmetic progression) for which the same exact counting still works.
3. **Formalize in Lean.** (i) The six-row table in 2.3 and the exactness-on-complete-residue-systems lemma. (ii) The commutator computation giving −3/8 and −9/32. (iii) Primitive-matrix computations for small p by `decide`. (iv) Cofinal Wall.
4. **Other bases.** Bases 2 and 3 are awkward: the orbit is live (3 ∤ x), and parity is determined by the previous step. Readouts other than the residue (e.g. leading ternary digits of x\_k) are an option.
5. **The 5x+1 and relatives.** The same machinery should apply to other affine families: the commutator-translation argument is the whole proof of irreducibility. In passing: the Researcher's Bible reports that the coordinate-version construction breaks structurally when q is a Wieferich prime (1093 and 3511 below 5000), and that this has not been ruled out. I have not re-derived it.

### 2.8 Scope and quantifiers

Each row states the exact quantifier. Nothing in one row implies another.

| Statement | Quantifier | Exceptions | Status |
| --- | --- | --- | --- |
| ERE (atomic) | for all targets w, primes p, residues r, bounds B, a predecessor exists | none | proved in your papers; status as stated there |
| Theorem A | Haar-almost every 3-adic seed | Haar-null, dense, uncountable | derived, sketch |
| Theorem B | all seeds in a complete residue system, finite horizon about L−2 steps | none, but no infinite orbit | derived, sketch |
| Spectral / density-one result (as you describe it) | density-one set of starting numbers, left-only | density-zero set | not re-derived here |
| One integer seed (e.g. 8) | one infinite orbit | n/a | open |

**Exceptional seeds exist in Z\_3 \[derived\].** A fixed point of T gives a constant residue sequence. T(x) = x gives x = μ/(2(μ−3)), and it must agree with the μ-table (μ depends on x mod 27). μ = 2: x = −1 ≡ 26, where μ = 2 ✓. μ = 4: x = 2, μ(2) = 4 ✓. μ = 16: x = 8/13; 13⁻¹ ≡ 25 mod 27, 8·25 = 200 ≡ 11, and μ(11) = 16 ✓. μ = 8: x = 4/5; 5⁻¹ ≡ 11, 4·11 = 44 ≡ 17, and μ(17) = 2 ≠ 8 ✗. So T has three fixed points (−1, 2, 8/13). Seeds that land on them, and seeds whose pattern avoids a fixed word, are exceptions. The second family is uncountable because avoiding a word still leaves positive entropy. That the exceptional set has full Hausdorff dimension is a conjecture (Besicovitch–Eggleston type), not shown here. So no all-seeds theorem exists in Z\_3.

*An explicit non-generic integer family \[derived by hand; family from the Researcher's Bible\].* Let x = 2 + 3^k·u with k ≥ 3 and 3 ∤ u. Then x ≡ 2 mod 27, so μ = 4, and T(x) = 4(2x−1)/6 = (2/3)(3 + 2·3^k·u) = 2 + 4·3^{k−1}·u, the same form with k one smaller. So the orbit stays in cell 2 for k − 2 left turns, and as k grows these seeds approach the fixed point 2 3-adically. Exceptional seeds therefore exist among the integers for as long a stretch as you like.

**Exceptional seeds exist among the integers too \[derived\].** C(G(n)) = n for every n: C(2n) = n, and C((n−1)/3) = 3·(n−1)/3 + 1 = n because (n−1)/3 is odd. So G inverts C, and a G-cycle read backwards is a Collatz cycle. The trivial cycle is a G-cycle: G(1) = 2, G(2) = 4, G(4) = 1. So seeds 1, 2, 4 have periodic left orbits, and any other G-cycle would be a nontrivial Collatz cycle.

**What follows \[conditional, not an impossibility theorem\].**

1. A theorem "every integer seed outside {1, 2, 4} has an unbounded, normal left orbit" would imply there is no nontrivial greedy Collatz cycle, a special case of the cycle problem, so it is at least that hard.
2. Whether such a theorem is impossible to prove is open. I have shown neither a proof nor an obstruction.
3. Normality for integer seeds needs an extra independent step: pattern diversity is necessary for the residue walk to equidistribute, not sufficient.

**Research direction, not a result \[untested\].** Averaging over integer seeds turns the pattern problem into Weyl sums with coefficients of the form 2^d/3^u. A Baker-type lower bound for |2^d − c·3^u| might supply the non-degeneracy needed.

### 2.9 The spectral-decay lemma: dyadic versus triadic

**Why it is dyadic.** In the Thorp argument each step averages conditional mass over a pair of positions (a fair binary coin). Noise created j steps ago is then spread over two disjoint subcubes of size 2^{j−1}, so its squared norm carries the weight 2^{−j}. That gives the paper's identity E\_t = Σ\_{j=1}^{d} 2^{−j} b\_{t−j} (Lemma 3.2).

**The scalar part for weight q^{−j} \[derived\].** Suppose E\_t = Σ q^{−j} b\_{t−j} and b\_s ≤ (1−β)E\_s + η. The induction E\_t ≤ γ^{t−c} + η/β closes if (1−β) Σ\_{j≥1} (qγ)^{−j} = (1−β)/(qγ − 1) ≤ 1, i.e. γ ≥ (2−β)/q. For q = 2 this is γ = 1 − β/2, which is the paper's 31/32 at β = 1/16. For q = 3 it is γ = (2−β)/3 ≈ 0.646. So the scalar recurrence adapts by replacing 2 with 3 throughout. I checked the geometric-series condition, not the full Lean proof.

**The structural part is not a corollary \[open\].** What must be re-derived is the identity E\_t = Σ q^{−j} b\_{t−j}. It uses coordinate averages that annihilate mean-zero vectors after one sweep, and noise on one-free-position switches. For q = 3 this means a Z\_3 analogue of Thorp: triples of positions cycled by an independent uniform element of Z\_3. That is a different shuffle.

**Relevance to the left branch \[low confidence\].** The left branch also refreshes one ternary coordinate per T-step (the lift digit s), but there is no cube-sweep structure, and the residue chain is finite, so its gap comes from Perron–Frobenius (2.4) with no Thorp machinery. The only place a quantitative energy argument might help is a p-uniform gap bound (the conjecture at the end of 2.4).

### 2.10 What the pure-Lean port of the atomic proof established

The file is AtomicERE\_pure.lean (about 2,000 lines, Lean core only). The statements below marked **\[checked in Lean\]** are theorems in that file. Anything marked otherwise was not formalized.

**1. Full fibres at every depth \[checked in Lean\].** Let p ≥ 5 be prime, v even, 3 ∤ v. For every depth J ≥ 1, every unit class c < 3^(J+1) and every residue r, there is an even tree node n ≡ c (mod 3^(J+1)) with n ≡ r (mod p) (`fibre_full`). The same holds for odd nodes (`fibre_full_odd`), and the stabilisation predicate holds from depth 1 (`stab_one`).

*Derivation.* The fibre sizes σ\_K are at most p, non-increasing in K, and equal to p at the depth where the proof stabilises. So σ\_K = p for every K ≥ 1.

*What this does not do.* It is a corollary of the density theorem, not a second proof of it. The proof of `fibre_full` for J below the stabilisation depth goes through that depth and projects down, and `stab_one` is derived from the theorem. So the non-effective stabilisation depth is not a separate obstruction on top of the real open question, a bound on the size of the witness n. A bound would need stabilisation at depth 1 *before* knowing the theorem, so that walks act on fibres at depth J itself.

**2. The obstruction needs only that 2 and 3 are invertible \[checked in Lean\].** For every modulus M ≥ 5 coprime to 6, prime or not, there is no flat assignment (`no_flat_coprime6`) and fibre sizes stabilise (`stabilization_coprime6`). In the file these parts use only the class `Inv23` (2 and 3 invertible), not a field.

**3. Where the generalisation stops \[checked in Lean, for the abstract lemma only\].** The step from "no flat assignment" to "the holonomy group contains a nonzero translation" divides by 1 − ℓ₀ whenever ℓ₀ ≠ 1, which needs a field. The abstract statement it proves (a subgroup of Aff(R) with no common fixed point contains a nonzero translation) is false for R = Z/55: the subgroup generated by t ↦ 36t + 11 has no common fixed point and no nonzero translation. Reason: 36 ≡ 1 (mod 5) and 36 ≡ 3 (mod 11), the element has order 5, and every nontrivial power has slope ≠ 1. The three `decide` facts `z55_no_common_fixed_point`, `z55_no_nonzero_translation` and `z55_generates_group_of_order_five` check this. It says nothing about the actual holonomy group of the state graph modulo 55.

**4. Composite moduli, numerically \[numeric\].** For M ∈ {25, 35, 49, 55, 65, 77, 85, 91, 121} and depths K = 1 and 2, the holonomy group of the state graph at the base point has size M·φ(M): the full group Z/M ⋊ units. It contains all M translations and has no common fixed point (appendix E). This is evidence at two depths only.

**5. Walks and holonomy under weaker hypotheses \[checked in Lean; this was "suspected" before\].** The unit-based versions are in the file. When 2 and 3 are invertible modulo M, walks and the holonomy group are closed under inverses and products (`Walk.symm`, `Hol_inv`), edges and walks map fibres onto fibres (`edge_image`, `walk_image`), and a common fixed point of the holonomy group yields a flat assignment (`flat_of_fixed`). So the *only* step that needs a field is `translation_of_no_fixed`, and density needs only a unit translation (`fibre_full_of_translation`). Section 2.11 takes this as its starting point.

**6. Dependency inventory \[read off the file\].** The arithmetic specific to q = 3 sits in Parts 2 and 3 (lifting-the-exponent for the base 4, the order of 2, the cycle of units) and in the explicit nodes used in the no-flat argument. Counting, stabilisation, walks, holonomy, the translation lemma and density are written against the edge definitions and the field property, not against 3. If you try 5x + 1 or similar, those q = 3 pieces are where changes would go (not tested).

### 2.11 Handover: unit translations in the holonomy group modulo composite M

**What a new assistant needs.** Two files: AtomicERE\_pure.lean (compile with `lean AtomicERE_pure.lean`, Lean 4.36.0-rc1, no imports, about 12 seconds) and this dossier. Names in `code` are in the file.

**A. The problem.** For a modulus M ≥ 5 coprime to 6, prove `UnitTranslation M` (Part 11 of the file), or find an M and a depth where it fails. In words: for every depth K ≥ 1 there is a unit d of Z/M and a closed walk at the base state (1, 0) of the depth-K state graph whose label is the map t ↦ t + d.

**B. Setting.** The depth-K state graph has states (c, f): c a unit mod 3^(K+1) (so 3 ∤ c) and f ∈ {0, 1}. Edges: D goes (c, f) → (2c mod 3^(K+1), 0) with label t ↦ 2t. U goes (e mod 3^(K+1), 0) → (((e−1)/3) mod 3^(K+1), 1) for e < 3^(K+2), e ≡ 1 mod 3, e ≢ 1 mod 9, with label t ↦ (t−1)/3. A walk may use edges forwards or backwards (a backward edge contributes the inverse label). `Hol K` is the set of labels of closed walks at (1, 0), a subgroup of Aff(Z/M). The fibre of a state is the set of residues mod M of tree nodes n with n ≡ c (mod 3^(K+1)) and n ≡ f (mod 2).

**C. Why this is the only missing hypothesis \[checked in Lean\].** `main_theorem_mod` proves the full theorem modulo any M ≥ 5 coprime to 6 from `UnitTranslation M`. Derivation of the density step: a translation (1, d) in `Hol K` maps the stabilised fibre of the base state onto itself (`walk_image`), so t in the fibre implies t + d in the fibre. The fibre is nonempty (the seed), so it contains t₀ + kd for all k; if d is a unit, taking k = (r − t₀)d⁻¹ reaches every residue r. All even fibres have equal size (`fibre_card_const`), so all are full, and projecting from depth max(K₀, J) to depth J gives the claim (`fibre_full_of_translation`). Everything before this step needs only that 2 and 3 are invertible (`Inv23`).

**D. Reductions.**

1. **Translations form an additive subgroup \[checked in Lean\].** `translation_add`, `translation_neg`, `translation_nsmul`: if (1, d₁) and (1, d₂) are in `Hol K`, so are (1, d₁ + d₂) and (1, −d₁). The set T\_K = {d : (1, d) ∈ Hol K} is therefore a subgroup of the cyclic group Z/M, i.e. T\_K = dZ/M for some d dividing M, and `UnitTranslation` at depth K is equivalent to T\_K = Z/M.
2. **One prime at a time \[derived\].** Let M = q₁⋯q\_s be squarefree. T\_K = Z/M iff for each i some d\_i ∈ T\_K is not divisible by q\_i. Derivation: if so, put d = Σ\_i (M/q\_i)·d\_i. Modulo q\_j only the term i = j survives, and it equals (M/q\_j)·d\_j, a unit mod q\_j. So d is a unit modulo every q\_j, hence modulo M, and d ∈ T\_K because T\_K is a group. (Prime powers need the same argument with q^e.)
3. **Projection is onto \[derived\].** Reducing labels mod q maps `Hol K` (mod M) onto `Hol K` (mod q): the same words give the same walks. By the prime case, for each q | M there is a closed walk with label ≡ (1, τ) mod q and τ ≠ 0. Its label modulo the other prime factors is whatever it is.

**E. Why abstract group theory cannot finish it \[checked in Lean\].** Over Z/55 the subgroup generated by h(t) = 36t + 11 has no common fixed point and no nonzero translation (`z55_*`). Mechanism: 36 ≡ 1 mod 5 and 36 ≡ 3 mod 11, where 3 has order 5. The translation mod 5 is glued to a slope of order 5 mod 11, so any power that cancels the slope mod 11 (k a multiple of 5) also cancels the translation mod 5. Over Z/25 the subgroup generated by t ↦ 6t + 1 has no fixed point and its translations are exactly the multiples of 5: nonzero, never units (`z25_*`). So a proof of `UnitTranslation` must use that `Hol K` is the closed-walk group of *this* graph.

**F. The key structure: slope-1 loops \[derived; checked on 14 certificates\].**

*Derivation.* Take a forward walk with A doublings and u undos. By the closed form of 2.1, applied to a node n it gives (2^A·n − C)/3^u, where C = Σ over the undo steps of 3^(number of undos before that step)·2^(number of doublings after it). So its label is t ↦ (2^A·t − C)/3^u, with slope 2^A·3^(−u) and translation part −C·3^(−u). The slope is 1 modulo M iff M divides 2^A − 3^u. In that case the label is the translation by d = −C·3^(−u), a unit iff gcd(C, M) = 1.

*Consequence.* **`UnitTranslation M` at depth K holds if there is a closed walk w at depth K with M | 2^A − 3^u and gcd(C, M) = 1.** It is also necessary: the forward graph is strongly connected and `Hol K` is a finite group, so every element is the label of a forward closed walk (a backward edge can be replaced by a forward path back plus a power of a forward cycle). The condition has the same shape as the Collatz cycle equation (2^S − 3^k)·n = N, with C playing the role of N.

*Data.* Every certificate in the file has this form:

| M | depth | A | u | 2^A − 3^u | C | d = −C/3^u |
| --- | --- | --- | --- | --- | --- | --- |
| 25 | 1 | 7 | 1 | 125 = 5·25 | 8 | 14 |
| 55 | 1 | 6 | 2 | 55 = 55 | 28 | 3 |
| 253 | 1 | 8 | 1 | 253 | 64 | 63 |
| 35 | 1 | 10 | 2 | 1015 = 35·29 | 88 | 33 |
| 91 | 1 | 12 | 6 | 3367 = 91·37 | 1522 | 25 |
| 385 | 1 | 18 | 6 | 261415 = 385·679 | 1522 | 347 |

The closing condition at depth K (the walk returns to class 1 mod 3^(K+1)) reads (2^A − C)/3^u ≡ 1 (mod 3^(K+1)), together with every undo being legal along the way. Since a legal word is the same thing as a real chain of tree nodes, the problem becomes: find integers n₀ ≡ n₁ ≡ 1 (mod 3^(K+1)) with n₁ = (2^A·n₀ − C)/3^u along a legal word, such that M | 2^A − 3^u and gcd(C, M) = 1.

**G. Data \[numeric; Python in appendix F, Lean in `holStats` and the certificates\].**

- For every M in \[5, 400\] coprime to 6 (132 moduli) at depth 1, and every M in \[5, 200\] coprime to 6 (66 moduli) at depth 2, a forward closed walk with a unit translation exists. No failure was found. The longest certificate has 74 steps (M = 323, depth 1) and 41 steps (M = 127, depth 2). Depth 3 was spot-checked for 25, 35, 49, 55.
- Group sizes (depth 1): |Hol| = M·φ(M) (the full group Z/M ⋊ units) for M = 25, 35, 49, 55, 65, 77, 85, 91, 121 and 155 (for 155 = 5·31 it is the full direct product of the mod-5 and mod-31 groups, so no gluing at all). For M = 253 and 385 it is half of that (the slopes generated by 2 and 3 form an index-2 subgroup). Translations are all of Z/M in every case.
- 15 certificates are kernel-checked in the file (`unit_translation_M_K`).

**H. Suggested next steps.**

1. **Formalize F in Lean.** Prove that `runCert` computes the label (2^A·i3^u, −i3^u·C) for the list's statistics (A, u, C), by induction on the list (D: C ↦ 2C; U: C ↦ C + 3^u). Then state the equivalence "unit translation at depth K ⇔ a legal closed word with M | 2^A − 3^u and gcd(C, M) = 1". This turns the open problem into a statement about integers.
2. **Prove existence for M = q^e and M = q·r.** Choose A and u as multiples of the multiplicative orders of 2 and 3 so that 2^A ≡ 3^u ≡ 1 (mod M), then satisfy the 3-adic closing condition and gcd(C, M) = 1 by a CRT or counting argument on words. The smallest solutions in the table (A, u) = (6, 2) for 55 and (8, 1) for 253 (where M = 2^A − 3^u exactly) suggest how.
3. **Search for a counterexample.** Use the integer reformulation to avoid the M²-sized graph: enumerate pairs (A, u) with M | 2^A − 3^u and test the 3-adic closing condition by dynamic programming over the 2·3^K states, tracking C mod M. Try larger M, depth 3 or 4, and M whose prime factors p have ord\_p(2) and ord\_p(3) sharing large factors (the Goursat mechanism in E).
4. **Goursat route.** Prove independence of Hol\_K(q) and Hol\_K(r) for coprime q, r (true numerically at 155, index 2 at 253 and 385).

**I. Cautions.** (i) The theorem needs the unit translation at every depth K ≥ 1 (precisely at depth max(K₀, J)); the evidence covers K ≤ 3 only. (ii) The Z/55 and Z/25 examples are about abstract subgroups and do not refute the actual holonomy group. (iii) A certificate is depth-specific and says nothing about other depths. (iv) The scan in appendix F is Python; only the certificates and the Z/55, Z/25 facts are kernel-checked.

## 3. BBP as a second specific-number problem

**Framing.** Normality of π and normality of a single left-only orbit are the same kind of problem: show that one specific deterministic sequence is generic. Results for almost every number (Borel; my Theorem A) or for an averaged family (Theorem B, Champernowne-type) do not decide any particular number. Specific numbers have been proved normal when their digits come from sparse, lacunary structure (Champernowne-type constructions; the explicit constants of Bailey–Crandall), but no such structure is known for π. BBP gives an exact digit formula, not independence. This section is a worked second instance of the specific-number problem, with π as the motivating example only. It claims nothing about π itself.

### 3.1 Exact setup (corrected)

BBP: π = Σ\_{k≥0} 16^{−k} r\_k, r\_k = 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6).

**Correction \[derived, checked at n = 10\].** The coefficients 4, −2, −1, −1 sum to 0, so the 1/n term cancels: r\_n = 15/(64n²) + O(n⁻³). Check: r\_10 ≈ 0.00218 versus 15/6400 ≈ 0.00234. So Σ r\_n converges, and the perturbation in the Bailey–Crandall recursion is O(n⁻²) (the note's O(1/n) is too weak).

With Y\_n = Σ\_{k≤n} 16^{n−k} r\_k and z\_n = {Y\_n} we have z\_n = {16 z\_{n−1} + r\_n}, and {16^nπ} = {z\_n + t\_n} with t\_n = Σ\_{m≥1} 16^{−m} r\_{n+m} ≈ 1/(64n²).

*Derivation (the size of r\_n).* 1/(8n+j) = (1/8n)(1 − j/(8n) + …). So r\_n = Σ c\_j/(8n+j) = (Σ c\_j)/(8n) − (Σ c\_j j)/(64 n²) + O(n⁻³), with c = (4, −2, −1, −1) at j = (1, 4, 5, 6). Σ c\_j = 4−2−1−1 = 0, and Σ c\_j j = 4 − 8 − 5 − 6 = −15. Hence r\_n ≈ +15/(64 n²). Numeric check at n = 10: exact 0.00218 versus 0.00234 from the leading term.

*Derivation (recursion and tail).* Splitting off the k = n term, Y\_n = Σ\_{k≤n} 16^{n−k} r\_k = 16 Y\_{n−1} + r\_n. Since π = Σ\_k 16^{−k} r\_k, we get 16^n π = Y\_n + t\_n with t\_n = Σ\_{m≥1} 16^{−m} r\_{n+m} ≈ r\_n Σ\_{m≥1} 16^{−m} = r\_n/15 ≈ 1/(64 n²). Reducing mod 1, z\_n = {Y\_n} satisfies z\_n = {16 z\_{n−1} + r\_n}, and {16^n π} differs from z\_n by t\_n → 0.

**Warning \[proved\].** This recursion is a tautology: z\_n differs from {16^nπ} by t\_n → 0. A claim about z\_n is Bailey–Crandall's Hypothesis A, i.e. normality of π in base 16. BBP is a *computation shortcut*, not a source of independence.

Odd-moduli rewriting (for n − k ≥ 1): 16^n π ≡ Σ\_{k\<n} \[ 4·16^{n−k}/(8k+1) − 2^{4(n−k)−1}/(2k+1) − 16^{n−k}/(8k+5) − 2^{4(n−k)−1}/(4k+3) \] + (k = n and tail terms) (mod 1).

*Derivation (odd moduli).* For m = n−k ≥ 1: (2/(8k+4))·16^m = 16^m/(4k+2) = 2^{4m−1}/(2k+1), and 16^m/(8k+6) = 2^{4m−1}/(4k+3), because 16^m/2 = 2^{4m−1} is an integer. So every remaining modulus (8k+1, 2k+1, 8k+5, 4k+3) is odd.

*Derivation (state vector).* Put u\_{n,k} = 16^{n−k} mod q\_k. Then u\_{n+1,k} = 16·u\_{n,k} mod q\_k, and the coordinate k = n+1 enters with value 16^0 = 1. So one step multiplies every existing coordinate by 16 and appends a new one.

Structure:

- Terms with m = n − k < log\_16(8k) are not reduced mod q: they are smooth deterministic real numbers.
- Terms with larger m are genuine modular exponentials: the value is 16^m mod q\_k over q\_k, with q\_k ∈ {8k+1, 2k+1, 8k+5, 4k+3}.
- State view: u\_{n,k} = 16^{n−k} mod q\_k. One step multiplies every coordinate by 16 and adds a new coordinate equal to 1. The output is a linear functional of u. It is a rotation of a growing product of cyclic groups.

### 3.2 Why "the ERE method" does not transfer verbatim

- ERE's power comes from *branching*: an ensemble of paths, with affine labels acting on fibres, and a non-coboundary condition forcing a translation.
- BBP is a single non-branching path.
- What can transfer: the idea "affine/rotation action on residue fibres plus a mixing/spectral argument". The ensemble must come from somewhere else.
- Natural candidates for an ensemble: (a) the time average over n, viewed as the orbit of a rotation on the product group Π Z/q\_k; (b) offsets n ≡ a (mod M), i.e. the base-16^M ladder; (c) a *family* of BBP-type numbers.

A metric argument over a continuous family (e.g. x(s) = Σ 16^{−k}/(8k+s)) proves normality for almost every s, but says nothing about s = 1, 4, 5, 6. So (c) alone does not decide π.

### 3.3 Reformulations of the targets

- **Hex disjunctiveness \[open\].** For every hex word w there is n with z\_n ∈ I\_w, an interval of length 16^{−|w|}. Equivalent: the ×16 orbit of π is dense.
- **Digit-level (full support) in hex \[open\].** Every hex digit appears. This is FS(16), the k = 4 rung for base 2, and it is much weaker than Disj(2).
- **Base 2 digit support is free.** Both binary digits occur for any irrational. By 1.2, Disj(2) ⇔ FS(2^k) for all k, so the real content starts at k ≥ 2.
- **Weyl form.** e(h·z\_n) is a *product* over the coordinates k. That is the structural obstacle: an exponential sum over n of a product of \~n factors.

### 3.4 Concrete sub-problems

- **P1 (single coordinate).** For prime q, h ≠ 0: Σ\_{m\<M} e(a·16^m/q) is o(M) for M ≥ q^ε, uniformly in a. Candidate tools: Korobov-type bounds and Bourgain–Glibichuk–Konyagin for multiplicative subgroups. *Not verified: I did not locate or read these statements. Treat as pointers only.*
- **P2 (orders).** ord\_q(16) is large for almost all q (Erdős–Murty-type results). Needed so that most coordinates have not wrapped around. *Not verified.*
- **P3 (joint behaviour).** Show that the factors e(h c\_j {16^{n−k}/q}) for different k are "effectively independent" as n varies. Idealized prediction: |average| ≈ Π\_k |E ψ\_k| decays exponentially in n. Rigor is the whole problem.
- **P4 (renewal shape).** The Lean lemma (E\_t = Σ 2^{−(j+1)} b\_{t−1−j} with b ≤ (1−β)E + η) is hard-wired to weights 2^{−(j+1)}. For a BBP recursion one would need a memory identity with base-16 weights. A general-weight version of the lemma is a small generalization, worth formalizing *only if* a recursion appears.
- **P5 (experiments).** Numerically estimate |avg e(h z\_n)| over windows, and test the product-independence heuristic across k. That tells you whether P3 is plausible before investing in proof.

### 3.5 Ideas \[idea\]

1. **Toy BBP with controlled moduli.** Study x = Σ\_k 16^{−k}/q\_k with pairwise coprime q\_k (e.g. primes). By CRT the coordinates are independent over a full period. Prove normality of a *specific* such number as a rehearsal for P3.
2. **Other bases.** BBP-type formulas exist for various constants in various bases (see Bailey's compendium of BBP-type formulas, 2004). Which constants and bases I did not check. Each is a separate specific-number problem.
3. **Hot-spot literature \[abstracts read, full papers not\].** Bailey–Crandall (Exp. Math. 10(2) (2001) 175–190) introduce Hypothesis A and show that normality of BBP-type constants would follow from it, so it is not a proof. Bailey–Crandall (Exp. Math. 11(4) (2002) 527–546) prove b-normality for a restricted class of explicit sums. Bailey–Misiurewicz (Proc. AMS 134 (2006) 2495–2501) prove: α is b-normal iff it has no base-b hot spot (see 1.8). Lagarias (Exp. Math. 10(3) (2001) 355–368) analyses Hypothesis A and points out the analogy with Furstenberg's conjecture.
4. **Honest expectation.** Normality of π via BBP is not expected from the methods in this dossier. The realistic output is the left-branch theory, the digit-to-word equivalence and the hot-spot reformulation, which stand on their own.

## 4. Roadmap

1. Formalize Cofinal Wall and the Ladder lemmas (short, self-contained).
2. Formalize the left-branch Markov-modulated chain: the six-row table, exactness over complete residue systems, the commutator translation, irreducibility mod M coprime to 6.
3. Prove Theorem A and Theorem B properly (variance bounds for growing gaps; boundary terms).
4. Quantify g\_cov(p) and |λ₂|(p): try to prove O(log p) and a uniform gap.
5. Test the 8-orbit against the generic law for 10⁷–10⁹ steps; look for deviations by class.
6. For BBP: run P5, then attack P1–P3 on the toy model. This tests the independence heuristic; it proves nothing about a specific number.

## 5. Pitfalls to remember

- Disjunctive never implies normal by itself. The bridge is irreducible + aperiodic + generic driver.
- Consecutive residues cannot be word-disjunctive; sample sparsely.
- The left-branch pattern is Markov-modulated, not i.i.d.
- A single orbit is a different problem from the tree.
- r\_n in BBP is O(n⁻²). The recursion for z\_n is a tautology unless you add arithmetic input.

Almost-every results and averaged constructions never decide a specific number. π (via BBP) and the 8-orbit share that obstruction.

## 6. Appendix: scripts behind the numeric claims

Run in this session (Python 3, numpy, sympy); the outputs are the numbers quoted in 2.3 and 2.4. No one else has run them.

**A. Greedy-orbit statistics (2.3).**

```python
import collections
n, U, D, N = 16, 0, 0, 60000
trace = []
for _ in range(N):
    if n % 18 in (4, 16): n = (n - 1)//3; U += 1; trace.append('U')
    else: n *= 2; D += 1; trace.append('D')
print(U/N, D/U)          # 0.300, 2.331
runs, r = collections.Counter(), 0
for c in trace:
    if c == 'D': r += 1
    else: runs[r] += 1; r = 0
tot = sum(runs.values())
print({k: round(v/tot, 3) for k, v in sorted(runs.items())})  # about {1:.22, 2:.449, 3:.11, 4:.221}
```

**B. All seeds, 3^11 (2.3 check).**

```python
import collections
cnt, pairs, tot = collections.Counter(), collections.Counter(), 0
for m in range(1, 3**11):
    n = 2*m
    if n % 3 == 0: continue
    runs, r, u = [], 0, 0
    while u < 8:
        if n % 18 in (4, 16): n = (n-1)//3; u += 1; runs.append(r); r = 0
        else: n *= 2; r += 1
    for i in range(1, 8): cnt[runs[i]] += 1; tot += 1
    for i in range(1, 7): pairs[(runs[i], runs[i+1])] += 1
print({k: round(v/tot, 4) for k, v in sorted(cnt.items())})   # 2/9, 4/9, 1/9, 2/9
print([(a, b) for a in range(1, 5) for b in range(1, 5) if pairs[(a, b)] == 0])  # (3,1),(3,3),(4,1),(4,3)
```

**C. Chain, covering length and spectral gap (2.4).**

```python
import numpy as np
table = {'A': [(4, 'A'), (4, 'B'), (16, 'A')], 'B': [(2, 'A'), (8, 'A'), (2, 'B')]}
idx = {'A': 0, 'B': 1}
def chain(p):
    M = np.zeros((2*p, 2*p)); inv6 = pow(6, -1, p)
    for c, rows in table.items():
        for mu, c2 in rows:
            for t in range(p):
                M[idx[c]*p + t, idx[c2]*p + (mu*(2*t - 1)*inv6) % p] += 1/3
    return M
def gcov(p):
    S = (chain(p) > 0).astype(int); A = np.eye(2*p, dtype=int); g = 0
    while A.min() == 0: A = ((A @ S) > 0).astype(int); g += 1
    return g
def lam2(p):
    ev = sorted(np.linalg.eigvals(chain(p)), key=lambda z: -abs(z))
    return abs(ev[1])
```

**D. Commutators in exact arithmetic (2.4).**

```python
from fractions import Fraction as F
f = lambda mu: (F(mu, 3), F(-mu, 6))
comp = lambda f, g: (g[0]*f[0], g[0]*f[1] + g[1])      # first f, then g
inv = lambda f: (1/f[0], -f[1]/f[0])
comm = lambda f, g: comp(comp(comp(f, g), inv(f)), inv(g))
print(comm(f(2), f(4)), comm(f(4), f(16)))            # (1, -3/8), (1, -9/32)
```

**E. Holonomy group of the state graph modulo M (2.10, item 4).**

```python
from math import gcd
from collections import deque
def hol(M, K):
    M3 = 3**(K+1); units = [c for c in range(M3) if c % 3]; i3 = pow(3, -1, M)
    edges = [((c, f), (2*c % M3, 0), (2 % M, 0)) for c in units for f in (0, 1)]
    edges += [((e % M3, 0), (((e-1)//3) % M3, 1), (i3, -i3 % M))
              for e in range(3**(K+2)) if e % 3 == 1 and e % 9 != 1]
    then = lambda f, g: (g[0]*f[0] % M, (g[0]*f[1] + g[1]) % M)
    def inv(f): i = pow(f[0], -1, M); return (i, -i*f[1] % M)
    nxt = {}
    for u, w, l in edges:
        nxt.setdefault(u, []).append((w, l)); nxt.setdefault(w, []).append((u, inv(l)))
    start = ((1, 0), (1, 0)); seen = {start}; dq = deque([start])
    while dq:
        u, lab = dq.popleft()
        for w, l in nxt.get(u, []):
            n = (w, then(lab, l))
            if n not in seen: seen.add(n); dq.append(n)
    return {lab for u, lab in seen if u == (1, 0)}
for M in (25, 35, 55, 91):
    for K in (1, 2):
        H = hol(M, K); T = {b for a, b in H if a == 1}
        g = M
        for b in T: g = gcd(g, b)
        fixed = [x for x in range(M) if all((a*x + b) % M == x for a, b in H)]
        print(M, K, len(H), len(T), g, len(fixed))  # |H| = M*phi(M), len(T) = M, g = 1, no fixed point
```

**F. Certificate search, slope-1 loop data and the scan (2.11).**

```python
from math import gcd
from collections import deque

def find(M, K):
    """Shortest forward closed walk at the base state whose label is a unit translation.
    Returns (steps, label); a step is 0 for D, or e > 0 for U taken from the lift e."""
    M3 = 3**(K+1); i3 = pow(3, -1, M); base = (1, 0)
    def succ(state):
        c, f = state
        yield 0, ((2*c) % M3, 0), (2 % M, 0)
        if f == 0:
            for j in range(3):
                e = c + M3*j
                if e % 3 == 1 and e % 9 != 1 and e < 3**(K+2):
                    yield e, (((e-1)//3) % M3, 1), (i3, (-i3) % M)
    then = lambda f, g: ((g[0]*f[0]) % M, (g[0]*f[1] + g[1]) % M)
    start = (base, (1, 0)); par = {start: None}; dq = deque([start])
    while dq:
        node = dq.popleft(); st, lab = node
        if st == base and lab[0] == 1 and lab[1] != 0 and gcd(lab[1], M) == 1:
            steps = []; cur = node
            while par[cur] is not None:
                prev, code = par[cur]; steps.append(code); cur = prev
            return steps[::-1], lab
        for code, nst, l in succ(st):
            n = (nst, then(lab, l))
            if n not in par: par[n] = (node, code); dq.append(n)
    return None

def loop_data(M, K):
    steps, lab = find(M, K)
    A = sum(1 for s in steps if s == 0); u = len(steps) - A
    C, ub = 0, 0
    for i, s in enumerate(steps):
        if s != 0:
            C += 3**ub * 2**sum(1 for t in steps[i+1:] if t == 0); ub += 1
    assert (2**A - 3**u) % M == 0 and gcd(C, M) == 1
    assert lab[1] == (-C * pow(3, -u, M)) % M      # d = -C / 3^u
    return A, u, C, lab[1]

def scan(K, lo, hi):
    return [M for M in range(lo, hi+1) if gcd(M, 6) == 1 and find(M, K) is None]

print(loop_data(55, 1))        # (6, 2, 28, 3)
print(scan(1, 5, 400), scan(2, 5, 200))   # [] []  (about 55 seconds in total)
```
