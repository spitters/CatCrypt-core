/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Ring

/-!
# Pratt/Lucas prime certificates over fast modular exponentiation

A reusable core for proving `Nat.Prime p` for large `p` via the Lucas primality
criterion, using a binary (square-and-multiply) modular exponentiation whose
result is checkable by kernel `decide` at cryptographic sizes.

The `ZMod p` power `a ^ (p - 1)` is unary `npowRec`, so it is not directly
evaluable for a 256-bit `p`. `powMod` computes `a ^ k % n` in `O(log k)`
multiplications, and `powMod_cast` transports a fast `powMod … = 1` check into
the `a ^ (p - 1) = 1` hypothesis of `lucas_primality`.

## Main definitions

* `powMod a k n` — binary modular exponentiation returning `a ^ k % n`.
* `Cert` — a Pratt certificate tree; `Cert.check` — its Boolean checker.
* `pratt_prime c` — tactic closing `Nat.Prime p` from an inline certificate `c`.

## Main results

* `powMod_eq` — `powMod a k n = a ^ k % n` for `0 < n`.
* `powMod_cast` — `((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k`.
* `lucas_of_cover` — `Nat.Prime p` from a witness `a`, a list `qs` containing every
  prime factor of `p - 1`, and fast `powMod` checks.
* `lucas_of_certificate` — the same from a list `qs` of prime factors with
  product `p - 1`.
* `Cert.sound` — `c.check = true → Nat.Prime c.prime`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.PrattCertificate

/-- Square-and-multiply worker for modular exponentiation. `fuel` bounds the number of
squarings; `base` is the running square, `e` the remaining exponent bits, and `acc` the
accumulated product, all kept reduced `% m`. The `e = 0` guard halts the loop, so the
recursion depth is the bit length of the initial exponent. -/
def powModGo (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,      _,    _, acc => acc
  | fuel+1, base, e, acc =>
      if e = 0 then acc else
        let acc' := if e % 2 = 1 then (acc * base) % m else acc
        powModGo m fuel ((base * base) % m) (e / 2) acc'

/-- Binary (square-and-multiply) modular exponentiation: `powMod a k n = a ^ k % n`
(for `0 < n`), computed in `O(log k)` multiplications. The worker `powModGo` is
tail-recursive with fuel `k`, so kernel `decide` reduces a fully applied `powMod` in
`O(log k)` GMP `Nat` steps at cryptographic sizes without a `Lean.ofReduceBool` axiom. -/
def powMod (a k n : ℕ) : ℕ := powModGo n k (a % n) k (1 % n)

/-- The worker invariant: cast into `ZMod m`, `powModGo` computes `acc * base ^ e`,
provided the fuel covers the exponent (`e < 2 ^ fuel`). -/
theorem powModGo_cast (m : ℕ) :
    ∀ (fuel base e acc : ℕ), e < 2 ^ fuel →
      ((powModGo m fuel base e acc : ℕ) : ZMod m) = (acc : ZMod m) * (base : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
      intro base e acc he
      have he0 : e = 0 := by simpa using he
      subst he0; simp [powModGo]
  | succ fuel ih =>
      intro base e acc he
      rw [powModGo]
      by_cases h0 : e = 0
      · subst h0; simp
      · simp only [h0, if_false]
        have hlt : e / 2 < 2 ^ fuel := by
          have : (2 : ℕ) ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
          omega
        rw [ih _ _ _ hlt]
        have hbase : (((base * base) % m : ℕ) : ZMod m) = (base : ZMod m) ^ 2 := by
          rw [ZMod.natCast_mod]; push_cast; ring
        rw [hbase]
        have hacc : (((if e % 2 = 1 then (acc * base) % m else acc) : ℕ) : ZMod m)
              = (acc : ZMod m) * (base : ZMod m) ^ (e % 2) := by
          by_cases h1 : e % 2 = 1
          · simp only [h1, if_true]; rw [ZMod.natCast_mod]; push_cast; ring
          · have : e % 2 = 0 := by omega
            simp [this]
        rw [hacc, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega

/-- The worker stays inside `[0, m)` when started from a reduced accumulator. -/
theorem powModGo_lt (m : ℕ) (hm : 0 < m) :
    ∀ (fuel base e acc : ℕ), acc < m → powModGo m fuel base e acc < m := by
  intro fuel
  induction fuel with
  | zero => intro base e acc h; simpa [powModGo]
  | succ fuel ih =>
      intro base e acc h
      rw [powModGo]
      by_cases h0 : e = 0
      · simp [h0, h]
      · simp only [h0, if_false]
        apply ih
        split
        · exact Nat.mod_lt _ hm
        · exact h

/-- The output is a residue: `powMod a k n < n` for `0 < n`. -/
theorem powMod_lt (a k n : ℕ) (hn : 0 < n) : powMod a k n < n :=
  powModGo_lt n hn k (a % n) k (1 % n) (Nat.mod_lt 1 hn)

/-- The fast `powMod` result cast into `ZMod n` equals the abstract power there,
so a `powMod … = 1` check discharges an `a ^ k = 1` hypothesis over `ZMod n`. -/
theorem powMod_cast (a k n : ℕ) [NeZero n] :
    ((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k := by
  rw [powMod, powModGo_cast n k (a % n) k (1 % n) Nat.lt_two_pow_self,
    ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_one, one_mul]

/-- Correctness of binary modular exponentiation. -/
theorem powMod_eq (a k n : ℕ) (hn : 0 < n) : powMod a k n = a ^ k % n := by
  have : NeZero n := ⟨by omega⟩
  have hml : a ^ k % n < n := Nat.mod_lt _ hn
  have hc : ((powMod a k n : ℕ) : ZMod n) = ((a ^ k % n : ℕ) : ZMod n) := by
    rw [powMod_cast, ZMod.natCast_mod, Nat.cast_pow]
  have hmeq := (ZMod.natCast_eq_natCast_iff _ _ _).mp hc
  rwa [Nat.ModEq, Nat.mod_eq_of_lt (powMod_lt a k n hn), Nat.mod_eq_of_lt hml] at hmeq

/-- A prime dividing the product of a list of primes is a member of the list. -/
theorem prime_mem_of_dvd_listProd {q : ℕ} (hq : q.Prime) :
    ∀ (l : List ℕ), (∀ r ∈ l, Nat.Prime r) → q ∣ l.prod → q ∈ l := by
  intro l
  induction l with
  | nil =>
    intro _ hd
    simp only [List.prod_nil, Nat.dvd_one] at hd
    exact absurd hd hq.ne_one
  | cons r t ih =>
    intro hl hd
    rw [List.prod_cons] at hd
    rcases (hq.dvd_mul).1 hd with h | h
    · exact List.mem_cons.mpr
        (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (hl r (List.mem_cons.mpr (Or.inl rfl)))).1 h))
    · exact List.mem_cons.mpr
        (Or.inr (ih (fun s hs => hl s (List.mem_cons.mpr (Or.inr hs))) h))

/-- Lucas primality from a covering list of prime factors. Given a witness `a`, a
list `qs` containing every prime factor of `p - 1`, the Fermat check
`powMod a (p - 1) p = 1`, and for each `q ∈ qs` the check
`powMod a ((p - 1) / q) p ≠ 1`, conclude `Nat.Prime p`. -/
theorem lucas_of_cover (p : ℕ) (hp1 : 1 < p) (a : ℕ) (qs : List ℕ)
    (hcover : ∀ q, Nat.Prime q → q ∣ p - 1 → q ∈ qs)
    (hfermat : powMod a (p - 1) p = 1)
    (hwit : ∀ q ∈ qs, powMod a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p := by
  have hp0 : 0 < p := by omega
  have : NeZero p := ⟨by omega⟩
  apply lucas_primality p (a : ZMod p)
  · have hc := powMod_cast a (p - 1) p
    rw [hfermat] at hc
    simpa using hc.symm
  · intro q hqp hqd
    have hqin : q ∈ qs := hcover q hqp hqd
    intro hcontra
    apply hwit q hqin
    have hc := powMod_cast a ((p - 1) / q) p
    rw [hcontra] at hc
    have hlt : powMod a ((p - 1) / q) p < p := powMod_lt a _ p hp0
    have heq : ((powMod a ((p - 1) / q) p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      rw [hc]; simp
    rw [ZMod.natCast_eq_natCast_iff] at heq
    unfold Nat.ModEq at heq
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp1] at heq
    exact heq

/-- Lucas primality via a certificate. Given a witness `a`, a list `qs` of the
prime factors of `p - 1` whose product is `p - 1`, the Fermat check
`powMod a (p - 1) p = 1`, and for each factor `q` the check
`powMod a ((p - 1) / q) p ≠ 1`, conclude `Nat.Prime p`. -/
theorem lucas_of_certificate (p : ℕ) (hp1 : 1 < p) (a : ℕ) (qs : List ℕ)
    (hprod : qs.prod = p - 1)
    (hqs_prime : ∀ q ∈ qs, Nat.Prime q)
    (hfermat : powMod a (p - 1) p = 1)
    (hwit : ∀ q ∈ qs, powMod a ((p - 1) / q) p ≠ 1) :
    Nat.Prime p :=
  lucas_of_cover p hp1 a qs
    (fun q hqp hqd => prime_mem_of_dvd_listProd hqp qs hqs_prime (by rw [hprod]; exact hqd))
    hfermat hwit

/-- The Fermat prime `2 ^ 16 + 1 = 65537`, proved via `lucas_of_certificate`.
Its `p - 1 = 2 ^ 16` has the single prime factor `2`; `3` is a witness. -/
theorem prime_65537 : Nat.Prime 65537 := by
  apply lucas_of_certificate 65537 (by norm_num) 3 (List.replicate 16 2)
  · decide
  · intro q hq
    rw [List.mem_replicate] at hq
    rw [hq.2]; exact Nat.prime_two
  · decide
  · intro q hq
    rw [List.mem_replicate] at hq
    rw [hq.2]; decide

/-! ## Reflective Pratt certificates

A `Cert` is a Pratt certificate tree. `Cert.check` is a Boolean checker that
reduces in the kernel by GMP-accelerated `Nat` arithmetic, and `Cert.sound` turns
`c.check = true` into `Nat.Prime c.prime`. The tactic `pratt_prime c` closes a
goal `Nat.Prime p` from an inline certificate `c` by kernel `decide`. -/

/-- `stripFactor q fuel n` divides `n` by `q` as long as `q > 1` divides it, at most
`fuel` times. -/
def stripFactor (q : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n =>
    if (decide (1 < q) && n % q == 0 && n != 0) = true then stripFactor q fuel (n / q) else n

/-- `stripFactor` removes a power of `q`: `n = stripFactor q fuel n * q ^ k`. -/
theorem stripFactor_spec (q : ℕ) :
    ∀ fuel n, ∃ k, n = stripFactor q fuel n * q ^ k := by
  intro fuel
  induction fuel with
  | zero => intro n; exact ⟨0, by simp [stripFactor]⟩
  | succ fuel ih =>
    intro n
    by_cases h : (decide (1 < q) && n % q == 0 && n != 0) = true
    · obtain ⟨k, hk⟩ := ih (n / q)
      refine ⟨k + 1, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [stripFactor, if_pos (by simp_all), pow_succ, ← mul_assoc, ← hk]
      exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1.2)).symm
    · exact ⟨0, by rw [stripFactor, if_neg h]; simp⟩

/-- `stripAll n qs` removes every power of every `q ∈ qs` from `n`. -/
def stripAll (n : ℕ) : List ℕ → ℕ
  | [] => n
  | q :: qs => stripAll (stripFactor q n n) qs

/-- If `stripAll n qs = 1`, every prime factor of `n` divides some `q ∈ qs`. -/
theorem dvd_mem_of_stripAll_eq_one {r : ℕ} (hr : r.Prime) :
    ∀ (qs : List ℕ) (n : ℕ), stripAll n qs = 1 → r ∣ n → ∃ q ∈ qs, r ∣ q := by
  intro qs
  induction qs with
  | nil =>
    intro n h hd
    simp only [stripAll] at h
    subst h
    exact absurd (Nat.dvd_one.1 hd) hr.ne_one
  | cons q qs ih =>
    intro n h hd
    simp only [stripAll] at h
    obtain ⟨k, hk⟩ := stripFactor_spec q n n
    rw [hk] at hd
    rcases (Nat.Prime.dvd_mul hr).1 hd with h1 | h1
    · obtain ⟨q', hq', hdq'⟩ := ih _ h h1
      exact ⟨q', List.mem_cons_of_mem _ hq', hdq'⟩
    · exact ⟨q, List.mem_cons_self, hr.dvd_of_dvd_pow h1⟩

/-- Trial division loop: `trialGo q fuel d` is `true` when no `m` with `d ≤ m` and
`m * m ≤ q` divides `q`, inspected for at most `fuel` candidates. -/
def trialGo (q : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d =>
    if q < d * d then true else if q % d == 0 then false else trialGo q fuel (d + 1)

/-- Soundness of `trialGo`. -/
theorem trialGo_spec (q : ℕ) :
    ∀ fuel d, trialGo q fuel d = true → ∀ m, d ≤ m → m * m ≤ q → ¬ m ∣ q := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [trialGo] at h
  | succ fuel ih =>
    intro d h m hdm hmq
    simp only [trialGo] at h
    by_cases h1 : q < d * d
    · exact absurd (lt_of_lt_of_le h1 (le_trans (Nat.mul_le_mul hdm hdm) hmq)) (lt_irrefl _)
    · rw [if_neg h1] at h
      by_cases h2 : q % d = 0
      · simp [h2] at h
      · simp only [beq_iff_eq, h2, if_false] at h
        rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
        · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
        · exact ih (d + 1) h m hlt hmq

/-- Primality by trial division up to `√q`. -/
def trialPrime (q : ℕ) : Bool := decide (2 ≤ q) && trialGo q q 2

/-- Soundness of `trialPrime`. -/
theorem trialPrime_sound (q : ℕ) (h : trialPrime q = true) : q.Prime := by
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq] at h
  by_contra hnp
  have hq0 : 0 < q := by omega
  have hq1 : q ≠ 1 := by omega
  have hsq := Nat.minFac_sq_le_self hq0 hnp
  have h2 : 2 ≤ q.minFac := (Nat.minFac_prime hq1).two_le
  exact trialGo_spec q q 2 h.2 q.minFac h2 (by rw [← pow_two]; exact hsq) (Nat.minFac_dvd q)

/-- A Pratt certificate tree. `small p` is checked by trial division;
`node p a fs` is a Lucas certificate for `p` with witness `a` whose list `fs`
certifies the distinct prime factors of `p - 1`. A numeral `n` denotes `small n`. -/
inductive Cert where
  | small (p : ℕ)
  | node (p a : ℕ) (fs : List Cert)

instance (n : ℕ) : OfNat Cert n := ⟨.small n⟩

/-- The prime a certificate is about. -/
def Cert.prime : Cert → ℕ
  | .small p => p
  | .node p _ _ => p

/-- The local Lucas checks of one node: `1 < p`, the Fermat check, the factors
`qs` cover `p - 1` (stripping them leaves `1`), and the witness checks. -/
def nodeOk (p a : ℕ) (qs : List ℕ) : Bool :=
  decide (1 < p) && powMod a (p - 1) p == 1 && stripAll (p - 1) qs == 1 &&
    qs.all (fun q => powMod a ((p - 1) / q) p != 1)

/-- `nodeOk` and primality of the factors give primality of `p`. -/
theorem prime_of_nodeOk (p a : ℕ) (qs : List ℕ) (hqs : ∀ q ∈ qs, q.Prime)
    (h : nodeOk p a qs = true) : p.Prime := by
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, hf⟩, hs⟩, hw⟩ := h
  refine lucas_of_cover p h1 a qs ?_ hf hw
  intro r hr hrd
  obtain ⟨q, hq, hrq⟩ := dvd_mem_of_stripAll_eq_one hr qs (p - 1) hs hrd
  rwa [(Nat.prime_dvd_prime_iff_eq hr (hqs q hq)).1 hrq]

mutual
/-- The Boolean checker of a Pratt certificate tree. -/
def Cert.check : Cert → Bool
  | .small p => trialPrime p
  | .node p a fs => nodeOk p a (fs.map Cert.prime) && Cert.checkAll fs

/-- `Cert.check` on every certificate of a list. -/
def Cert.checkAll : List Cert → Bool
  | [] => true
  | c :: cs => c.check && Cert.checkAll cs
end

mutual
/-- Soundness of `Cert.check`. -/
theorem Cert.sound : ∀ c : Cert, c.check = true → c.prime.Prime
  | .small p, h => trialPrime_sound p (by simpa [Cert.check] using h)
  | .node p a fs, h => by
    simp only [Cert.check, Bool.and_eq_true] at h
    refine prime_of_nodeOk p a _ ?_ h.1
    intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
    exact Cert.sound_all fs h.2 c hc

/-- Soundness of `Cert.checkAll`. -/
theorem Cert.sound_all : ∀ cs : List Cert, Cert.checkAll cs = true → ∀ c ∈ cs, c.prime.Prime
  | [], _, c, hc => absurd hc List.not_mem_nil
  | c :: cs, h, c', hc' => by
    simp only [Cert.checkAll, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hc' with heq | hc'
    · rw [heq]; exact Cert.sound c h.1
    · exact Cert.sound_all cs h.2 c' hc'
end

/-- `pratt_prime c` closes a goal `Nat.Prime p` from a Pratt certificate tree `c`
with `c.prime = p`, checking `c.check = true` by kernel reduction. -/
macro "pratt_prime " c:term : tactic =>
  `(tactic| exact CatCrypt.PrattCertificate.Cert.sound $c (by decide +kernel))

end CatCrypt.PrattCertificate
