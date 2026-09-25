/-!
# JSP-000216 / Erdős 245: a core-Lean interface

This file deliberately uses only Lean's core library.  It records the
set-theoretic part of the problem and proves the elementary facts that do not
depend on analysis.  The analytic statement in the catalogue uses `Set`,
`Filter`, `EReal`, and real division; those are Mathlib interfaces and are not
silently replaced here by a weaker theorem.  The definitions below therefore
serve as a dependency-free kernel for the eventual Mathlib formalisation.

The original problem asks for every infinite zero-density `A ⊆ ℕ`:

`limsup |(A + A) ∩ [1,N]| / |A ∩ [1,N]| ≥ 3`.

No unproved axiom or placeholder theorem is introduced in this file.
-/

namespace JSP000216

set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Classical

/- A subset of the natural numbers, represented without importing Mathlib. -/
abbrev NatSet := Nat → Prop

/- Unboundedness is equivalent to infinitude for subsets of `ℕ`; this is the
   formulation that is convenient for elementary core-Lean arguments. -/
def Infinite (A : NatSet) : Prop :=
  ∀ n : Nat, ∃ a : Nat, n < a ∧ A a

/- The additive sumset. -/
def SumSet (A : NatSet) : NatSet :=
  fun n => ∃ a b : Nat, A a ∧ A b ∧ a + b = n

/- Number of elements of `A` in the positive interval `[1,N]`. -/
def countPos : NatSet → Nat → Nat
  | _, 0 => 0
  | A, n + 1 => countPos A n + if A (n + 1) then 1 else 0

/- A natural-number formulation of density zero.  It is an interface only:
   the catalogue's real-valued limit is to be connected to it in a Mathlib
   development, rather than being silently identified with it. -/
def ZeroDensity (A : NatSet) : Prop :=
  ∀ k : Nat, 0 < k → ∃ N : Nat, ∀ n : Nat, N ≤ n →
    k * countPos A n ≤ n

theorem countPos_le (A : NatSet) : ∀ N : Nat, countPos A N ≤ N := by
  classical
  intro N
  induction N with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      by_cases h : A (n + 1) <;> simp [countPos, h] <;> omega

theorem countPos_mono (A : NatSet) : ∀ {m n : Nat}, m ≤ n →
    countPos A m ≤ countPos A n := by
  classical
  intro m n h
  induction h with
  | refl => exact Nat.le_refl _
  | @step n h ih =>
      simp only [countPos]
      omega

/- Enlarging the underlying set can only increase the interval count.  This
   is the counting-set analogue of `countPos_mono` and is useful when a
   finite structural argument is applied to a subset of the original set. -/
theorem countPos_mono_left {A B : NatSet}
    (hAB : ∀ n, A n → B n) :
    ∀ N : Nat, countPos A N ≤ countPos B N := by
  intro N
  induction N with
  | zero => exact Nat.le_refl _
  | succ n ih =>
      by_cases ha : A (n + 1)
      · have hb : B (n + 1) := hAB (n + 1) ha
        simp [countPos, ha, hb]
        omega
      · by_cases hb : B (n + 1)
        · simp [countPos, ha, hb]
          omega
        · simp [countPos, ha, hb]
          exact ih

theorem zeroDensity_mono {A B : NatSet}
    (hAB : ∀ n, A n → B n) (hB : ZeroDensity B) :
    ZeroDensity A := by
  intro k hk
  obtain ⟨N, hN⟩ := hB k hk
  refine ⟨N, ?_⟩
  intro n hn
  exact Nat.le_trans
    (Nat.mul_le_mul_left k (countPos_mono_left hAB n))
    (hN n hn)

theorem countPos_add_one_of_mem {A : NatSet} {m n : Nat}
    (hmn : m < n) (hn : A n) (hn_pos : 0 < n) :
    countPos A m + 1 ≤ countPos A n := by
  induction n generalizing m with
  | zero => omega
  | succ n ih =>
      have hmn' : m ≤ n := by omega
      have hmono := countPos_mono A hmn'
      simp [countPos, hn]
      omega

theorem countPos_pos_of_mem {A : NatSet} {a N : Nat}
    (ha : A a) (ha_pos : 0 < a) (haN : a ≤ N) : 0 < countPos A N := by
  classical
  induction N generalizing a with
  | zero => omega
  | succ n ih =>
      by_cases hlast : a = n + 1
      · subst hlast
        simp [countPos, ha]
      · have ha_le : a ≤ n := by omega
        have ih' := ih ha ha_pos ha_le
        by_cases h : A (n + 1) <;> simp [countPos, h] <;> omega

theorem sumSet_mem {A : NatSet} {a b : Nat}
    (ha : A a) (hb : A b) : SumSet A (a + b) := by
  exact ⟨a, b, ha, hb, rfl⟩

theorem sumSet_infinite {A : NatSet} (hA : Infinite A) : Infinite (SumSet A) := by
  obtain ⟨b, hb_gt, hb⟩ := hA 0
  intro n
  obtain ⟨a, ha_gt, ha⟩ := hA n
  refine ⟨a + b, ?_, sumSet_mem ha hb⟩
  omega

theorem infinite_nonempty {A : NatSet} (hA : Infinite A) : ∃ a, A a := by
  obtain ⟨a, _, ha⟩ := hA 0
  exact ⟨a, ha⟩

theorem countPos_unbounded {A : NatSet} (hA : Infinite A) :
    ∀ K : Nat, ∃ N : Nat, K ≤ N ∧ 0 < countPos A N := by
  classical
  intro K
  obtain ⟨a, ha_gt, ha⟩ := hA K
  refine ⟨a, by omega, countPos_pos_of_mem ha (by omega) (by omega)⟩

theorem countPos_eventually_pos {A : NatSet} (hA : Infinite A) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → 0 < countPos A n := by
  obtain ⟨a, ha_gt, ha⟩ := hA 0
  refine ⟨a, ?_⟩
  intro n hn
  exact countPos_pos_of_mem ha ha_gt hn

/- Every sumset element has an explicit pair of witnesses.  This converse is
   useful when a future finite-cardinality development introduces a truncated
   sumset. -/
theorem mem_sumSet_iff {A : NatSet} {n : Nat} :
    SumSet A n ↔ ∃ a b : Nat, A a ∧ A b ∧ a + b = n := by
  rfl

/- The exact analytic target is intentionally exposed as a named interface,
   so that a Mathlib file can instantiate it without changing the elementary
   definitions above.  `analyticConclusion` is a parameter, not an axiom: this
   theorem only says that an implementation of the analytic theorem implies
   the corresponding catalogue-shaped proposition. -/
def Erdos245Exact (analyticConclusion : NatSet → Prop) : Prop :=
  ∀ A : NatSet, Infinite A → ZeroDensity A → analyticConclusion A

theorem exact_of_analytic (analyticConclusion : NatSet → Prop)
    (h : ∀ A : NatSet, Infinite A → ZeroDensity A → analyticConclusion A) :
    Erdos245Exact analyticConclusion := by
  exact h

/- An exact integer inequality at infinitely many cutoffs is stronger than a
   real limsup bound (a ratio can approach 3 from below).  Keep it available
   as a diagnostic statement, but do not use it as the catalogue interface. -/
def DiscreteThreeExact (A : NatSet) : Prop :=
  ∀ M : Nat, ∃ N : Nat, M ≤ N ∧
    3 * countPos A N ≤ countPos (SumSet A) N

/- The correct discrete approximation to `limsup ratio ≥ 3`: for every
   reciprocal error `1/k`, the ratio is at least `3 - 1/k` at arbitrarily large
   cutoffs.  The eventual Mathlib layer proves equivalence with the EReal
   limsup statement once the denominator is eventually positive. -/
def DiscreteThreeApprox (A : NatSet) : Prop :=
  ∀ k : Nat, 0 < k → ∀ M : Nat, ∃ N : Nat, M ≤ N ∧
    (3 * k - 1) * countPos A N ≤ k * countPos (SumSet A) N

/- The corresponding constant-2 statement is a useful consequence of the
   approximation interface: take the reciprocal error parameter `k = 1`. -/
def DiscreteTwo (A : NatSet) : Prop :=
  ∀ M : Nat, ∃ N : Nat, M ≤ N ∧
    2 * countPos A N ≤ countPos (SumSet A) N

theorem discreteThreeExact_implies_approx {A : NatSet}
    (hA : DiscreteThreeExact A) : DiscreteThreeApprox A := by
  intro k hk M
  obtain ⟨N, hMN, hN⟩ := hA M
  refine ⟨N, hMN, ?_⟩
  have hnonneg : 0 ≤ countPos A N := Nat.zero_le _
  have hcoef : 3 * k - 1 ≤ 3 * k := by omega
  have hscale : (3 * k) * countPos A N ≤ k * countPos (SumSet A) N := by
    calc
      (3 * k) * countPos A N = k * (3 * countPos A N) := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ ≤ k * countPos (SumSet A) N := Nat.mul_le_mul_left k hN
  exact Nat.le_trans (Nat.mul_le_mul_right (countPos A N) hcoef) hscale

theorem discreteThreeApprox_implies_two {A : NatSet}
    (hA : DiscreteThreeApprox A) : DiscreteTwo A := by
  intro M
  obtain ⟨N, hMN, hN⟩ := hA 1 (by omega) M
  refine ⟨N, hMN, ?_⟩
  simpa using hN

/- The approximation interface is monotone in its reciprocal error parameter:
   a witness for `k` also witnesses every positive `j ≤ k`.  This is useful
   when a later analytic bridge chooses a convenient error scale.  The proof
   keeps all products in `Nat`; the key coefficient inequality is obtained by
   subtracting the ordered constants `j ≤ k` from the common term `3 * j * k`.
   No real-valued or limit assumption is used here. -/
theorem discreteThreeApprox_mono {A : NatSet}
    (hA : DiscreteThreeApprox A) {j k : Nat}
    (hj : 0 < j) (hjk : j ≤ k) :
    ∀ M : Nat, ∃ N : Nat, M ≤ N ∧
      (3 * j - 1) * countPos A N ≤ j * countPos (SumSet A) N := by
  intro M
  obtain ⟨N, hMN, hN⟩ := hA k (by omega) M
  refine ⟨N, hMN, ?_⟩
  let a := countPos A N
  let b := countPos (SumSet A) N
  have hcoef : k * (3 * j - 1) ≤ j * (3 * k - 1) := by
    have hsub : 3 * (k * j) - k ≤ 3 * (k * j) - j :=
      Nat.sub_le_sub_left hjk (3 * (k * j))
    calc
      k * (3 * j - 1) = 3 * (k * j) - k := by
        rw [Nat.mul_sub_left_distrib]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3 * (k * j) - j := hsub
      _ = j * (3 * k - 1) := by
        rw [Nat.mul_sub_left_distrib]
        simp [Nat.mul_assoc, Nat.mul_comm]
  have hscaled :
      (k * (3 * j - 1)) * a ≤ (j * (3 * k - 1)) * a :=
    Nat.mul_le_mul_right a hcoef
  have hscaled' :
      (j * (3 * k - 1)) * a ≤ (j * k) * b := by
    calc
      (j * (3 * k - 1)) * a = j * ((3 * k - 1) * a) := by
        simp [Nat.mul_assoc]
      _ ≤ j * (k * b) := Nat.mul_le_mul_left j hN
      _ = (j * k) * b := by simp [Nat.mul_assoc]
  have hcombine :
      (k * (3 * j - 1)) * a ≤ (j * k) * b :=
    Nat.le_trans hscaled hscaled'
  have hcombine' :
      k * ((3 * j - 1) * a) ≤ k * (j * b) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcombine
  have hresult : (3 * j - 1) * a ≤ j * b :=
    Nat.le_of_mul_le_mul_left hcombine' (by omega)
  simpa [a, b] using hresult

def DiscreteErdos245 : Prop :=
  ∀ A : NatSet, Infinite A → ZeroDensity A → DiscreteThreeApprox A

/- A finite-cardinality-free way of saying that a set contains at least `m`
   distinct elements.  The eventual Mathlib layer can turn this witness into
   a `Finset.card` inequality. -/
def InjectiveBelow (f : Nat → Nat) (m : Nat) : Prop :=
  ∀ ⦃i j : Nat⦄, i < m → j < m → f i = f j → i = j

def HasDistinctWitnesses (S : NatSet) (m : Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ i, i < m → S (f i)) ∧ InjectiveBelow f m

/- The positive truncation of a sumset that occurs in the Erdos problem. -/
def TruncatedSumSet (A : NatSet) (N : Nat) : NatSet :=
  fun s => SumSet A s ∧ 1 ≤ s ∧ s ≤ N

theorem truncatedSumSet_subset_sumSet {A : NatSet} {N s : Nat}
    (hs : TruncatedSumSet A N s) : SumSet A s :=
  hs.1

theorem truncatedSumSet_mono {A : NatSet} {M N : Nat} (hMN : M ≤ N) :
    ∀ ⦃s : Nat⦄, TruncatedSumSet A M s → TruncatedSumSet A N s := by
  intro s hs
  exact ⟨hs.1, hs.2.1, Nat.le_trans hs.2.2 hMN⟩

theorem truncatedSumSet_mono_left {A B : NatSet} {N : Nat}
    (hAB : ∀ s, A s → B s) :
    ∀ ⦃s : Nat⦄, TruncatedSumSet A N s → TruncatedSumSet B N s := by
  intro s hs
  rcases hs with ⟨⟨a, b, ha, hb, hab⟩, hpos, hle⟩
  exact ⟨⟨a, b, hAB a ha, hAB b hb, hab⟩, hpos, hle⟩

def StrictlyIncreasingOn (x : Nat → Nat) (n : Nat) : Prop :=
  ∀ ⦃i j : Nat⦄, i < n → j < n → i < j → x i < x j

theorem countPos_ge_of_strict {A : NatSet} {f : Nat → Nat} {m N : Nat}
    (hmem : ∀ i, i < m → A (f i) ∧ 0 < f i)
    (hstrict : StrictlyIncreasingOn f m)
    (hbound : ∀ i, i < m → f i ≤ N) :
    m ≤ countPos A N := by
  induction m generalizing N with
  | zero => omega
  | succ m ih =>
      by_cases hmzero : m = 0
      · subst hmzero
        have h0 := hmem 0 (by omega)
        exact countPos_pos_of_mem h0.1 h0.2 (hbound 0 (by omega))
      · have hmpos : 0 < m := by omega
        have hlast := hmem m (by omega)
        have hprefix_mem : ∀ i, i < m → A (f i) ∧ 0 < f i := by
          intro i hi
          exact hmem i (by omega)
        have hprefix_strict : StrictlyIncreasingOn f m := by
          intro i j hi hj hij
          exact hstrict (by omega) (by omega) hij
        have hprefix_bound : ∀ i, i < m → f i ≤ f (m - 1) := by
          intro i hi
          by_cases heq : i = m - 1
          · simp [heq]
          · have hilt : i < m - 1 := by omega
            have hlt := hprefix_strict (by omega) (by omega) hilt
            omega
        have hprefix := ih (N := f (m - 1)) hprefix_mem hprefix_strict hprefix_bound
        have hstep := countPos_add_one_of_mem
          (m := f (m - 1)) (n := f m)
          (hstrict (by omega) (by omega) (by omega)) hlast.1 hlast.2
        have hmono := countPos_mono A (hbound m (by omega))
        omega

def StrictlyIncreasingUpTo (x : Nat → Nat) (n : Nat) : Prop :=
  ∀ ⦃i j : Nat⦄, i ≤ n → j ≤ n → i < j → x i < x j

theorem infinite_has_positive_prefix {A : NatSet} (hA : Infinite A) :
    ∀ n : Nat, ∃ x : Nat → Nat,
      (∀ i, i ≤ n → A (x i) ∧ 0 < x i) ∧
      StrictlyIncreasingUpTo x n := by
  intro n
  induction n with
  | zero =>
      obtain ⟨a, ha_gt, ha⟩ := hA 0
      refine ⟨fun _ => a, ?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        exact ⟨ha, ha_gt⟩
      · intro i j hi hj hij
        omega
  | succ n ih =>
      obtain ⟨x, hx, hstrict⟩ := ih
      obtain ⟨y, hy_gt, hy⟩ := hA (x n)
      let x' : Nat → Nat := fun i => if i = n + 1 then y else x i
      refine ⟨x', ?_, ?_⟩
      · intro i hi
        by_cases hlast : i = n + 1
        · subst hlast
          simpa [x'] using (show A y ∧ 0 < y from ⟨hy, by omega⟩)
        · have hi_old : i ≤ n := by omega
          simpa [x', hlast] using hx i hi_old
      · intro i j hi hj hij
        by_cases hjlast : j = n + 1
        · by_cases hielast : i = n
          · subst hielast
            subst hjlast
            simp [x']
            exact hy_gt
          · have hi_old : i ≤ n := by omega
            have hi_lt_n : i < n := by omega
            subst hjlast
            have hilast : i ≠ n + 1 := by omega
            simp [x', hilast]
            have hold := hstrict hi_old (by omega : n ≤ n) hi_lt_n
            exact Nat.lt_trans hold hy_gt
        · have hj_old : j ≤ n := by omega
          have hi_old : i ≤ n := by omega
          have hilast : i ≠ n + 1 := by omega
          simpa [x', hjlast, hilast] using hstrict hi_old hj_old hij

theorem infinite_has_increasing_witness {A : NatSet} (hA : Infinite A) :
    ∀ n : Nat, ∃ x : Nat → Nat,
      (∀ i, i < n → A (x i)) ∧
      (∀ i, i < n → 0 < x i) ∧
      StrictlyIncreasingOn x n := by
  intro n
  cases n with
  | zero =>
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro i hi
        omega
      · intro i hi
        omega
      · intro i j hi hj hij
        omega
  | succ n =>
      obtain ⟨x, hx, hstrict⟩ := infinite_has_positive_prefix hA n
      refine ⟨x, ?_, ?_, ?_⟩
      · intro i hi
        exact (hx i (by omega)).1
      · intro i hi
        exact (hx i (by omega)).2
      · intro i j hi hj hij
        exact hstrict (by omega) (by omega) hij

/- The standard “two boundary chains” of sums: first `x 0 + x k`, then
   `x (k-n+1) + x (n-1)`.  The two chains are separated by the middle gap. -/
def boundarySum (x : Nat → Nat) (n k : Nat) : Nat :=
  if k < n then x 0 + x k else x (k - n + 1) + x (n - 1)

def threeBlockSum (x : Nat → Nat) (n k : Nat) : Nat :=
  if k < 2 * n - 1 then boundarySum x n k
  else x n + x (k - (2 * n - 1))

theorem boundarySum_strict {x : Nat → Nat} {n : Nat}
    (hn : 2 ≤ n) (hstrict : StrictlyIncreasingOn x n) :
    ∀ ⦃i j : Nat⦄, i < 2 * n - 1 → j < 2 * n - 1 → i < j →
      boundarySum x n i < boundarySum x n j := by
  intro i j hi hj hij
  by_cases hi0 : i < n
  · by_cases hj0 : j < n
    · simp [boundarySum, hi0, hj0]
      have hlt := hstrict (by omega) (by omega) hij
      omega
    · have hjn : n ≤ j := by omega
      have hjidx : j - n + 1 < n := by omega
      have hupper_i : x i ≤ x (n - 1) := by
        by_cases hilast : i = n - 1
        · simp [hilast]
        · have hiltn : i < n - 1 := by omega
          have hltx := hstrict (by omega) (by omega) hiltn
          omega
      have hlower_j : x 1 ≤ x (j - n + 1) := by
        by_cases hjone : j - n + 1 = 1
        · simp [hjone]
        · have hjone' : 1 < j - n + 1 := by omega
          have hltx := hstrict (by omega) hjidx hjone'
          omega
      have h01 := hstrict (by omega : 0 < n) (by omega : 1 < n) (by omega : 0 < 1)
      simp [boundarySum, hi0, hj0]
      omega
  · have hin : n ≤ i := by omega
    have hjn : n ≤ j := by omega
    have hiidx : i - n + 1 < n := by omega
    have hjidx : j - n + 1 < n := by omega
    have hidx : i - n + 1 < j - n + 1 := by omega
    have hj0 : ¬ j < n := by omega
    simp [boundarySum, hi0, hj0]
    have hlt := hstrict hiidx hjidx hidx
    omega

theorem boundarySum_le_twice_last {x : Nat → Nat} {n : Nat}
    (hn : 2 ≤ n) (hstrict : StrictlyIncreasingOn x n) :
    ∀ ⦃k : Nat⦄, k < 2 * n - 1 → boundarySum x n k ≤ 2 * x (n - 1) := by
  intro k hk
  by_cases hkn : k < n
  · have h0 : x 0 ≤ x (n - 1) := by
      by_cases hEq : n - 1 = 0
      · simp [hEq]
      · have hlt : 0 < n - 1 := by omega
        have hltx := hstrict (by omega) (by omega) hlt
        omega
    have hklt : k < n := hkn
    have hkupper : x k ≤ x (n - 1) := by
      by_cases hEq : k = n - 1
      · simp [hEq]
      · have hlt : k < n - 1 := by omega
        have hltx := hstrict (by omega) (by omega) hlt
        omega
    simp [boundarySum, hkn]
    omega
  · have hkn' : n ≤ k := by omega
    have hidx : k - n + 1 < n := by omega
    have hidxupper : x (k - n + 1) ≤ x (n - 1) := by
      by_cases hEq : k - n + 1 = n - 1
      · simp [hEq]
      · have hlt : k - n + 1 < n - 1 := by omega
        have hltx := hstrict (by omega) (by omega) hlt
        omega
    simp [boundarySum, hkn]
    omega

theorem boundarySum_mem {A : NatSet} {x : Nat → Nat} {n k : Nat}
    (hx : ∀ i, i < n → A (x i)) (hk : k < 2 * n - 1) :
    SumSet A (boundarySum x n k) := by
  by_cases hkn : k < n
  · simp [boundarySum, hkn]
    exact sumSet_mem (hx 0 (by omega)) (hx k hkn)
  · have hkn' : n ≤ k := by omega
    have hj : k - n + 1 < n := by omega
    simp [boundarySum, hkn]
    exact sumSet_mem (hx (k - n + 1) hj) (hx (n - 1) (by omega))

theorem boundarySum_mem_truncated {A : NatSet} {x : Nat → Nat} {n N k : Nat}
    (hx : ∀ i, i < n → A (x i))
    (hx_pos : ∀ i, i < n → 0 < x i)
    (hx_le : ∀ i, i < n → x i ≤ N)
    (hk : k < 2 * n - 1) :
    TruncatedSumSet A (2 * N) (boundarySum x n k) := by
  have hsum : SumSet A (boundarySum x n k) := boundarySum_mem hx hk
  by_cases hkn : k < n
  · have h0pos := hx_pos 0 (by omega)
    have hkpos := hx_pos k hkn
    have h0le := hx_le 0 (by omega)
    have hkle := hx_le k hkn
    refine ⟨hsum, ?_, ?_⟩
    · simp [boundarySum, hkn]
      omega
    · simp [boundarySum, hkn]
      omega
  · have hkn' : n ≤ k := by omega
    have hi : k - n + 1 < n := by omega
    have hipos := hx_pos (k - n + 1) hi
    have hlastpos := hx_pos (n - 1) (by omega)
    have hile := hx_le (k - n + 1) hi
    have hlastle := hx_le (n - 1) (by omega)
    refine ⟨hsum, ?_, ?_⟩
    · simp [boundarySum, hkn]
      omega
    · simp [boundarySum, hkn]
      omega

theorem threeBlockSum_mem_truncated {A : NatSet} {x : Nat → Nat}
    {n N k : Nat}
    (hn : 2 ≤ n)
    (hx : ∀ i, i < n + 1 → A (x i))
    (hx_pos : ∀ i, i < n + 1 → 0 < x i)
    (hx_le : ∀ i, i < n + 1 → x i ≤ N)
    (hstrict : StrictlyIncreasingOn x (n + 1))
    (hgap : 2 * x (n - 1) < x n + x 0)
    (hk : k < 3 * n - 1) :
    TruncatedSumSet A (x n + x (n - 1)) (threeBlockSum x n k) := by
  by_cases hfirst : k < 2 * n - 1
  · have hbase := boundarySum_mem_truncated
      (n := n) (N := N) (k := k)
      (fun i hi => hx i (by omega))
      (fun i hi => hx_pos i (by omega))
      (fun i hi => hx_le i (by omega)) hfirst
    have hsum : SumSet A (threeBlockSum x n k) := by
      simpa [threeBlockSum, hfirst] using hbase.1
    have hpos : 1 ≤ threeBlockSum x n k := by
      have hbasepos := hbase.2.1
      simpa [threeBlockSum, hfirst] using hbasepos
    have hupper : threeBlockSum x n k ≤ x n + x (n - 1) := by
      have hle_last := boundarySum_le_twice_last (x := x) hn
        (fun i j hi hj hij => hstrict (by omega) (by omega) hij) hfirst
      simp only [threeBlockSum, if_pos hfirst]
      have h0last : x 0 ≤ x (n - 1) := by
        by_cases hEq : n - 1 = 0
        · simp [hEq]
        · have hlt : 0 < n - 1 := by omega
          have hltx := hstrict (by omega) (by omega) hlt
          omega
      omega
    exact ⟨hsum, hpos, hupper⟩
  · have hsecond : 2 * n - 1 ≤ k := by omega
    have hidx : k - (2 * n - 1) < n := by omega
    have hsum : SumSet A (threeBlockSum x n k) := by
      simp [threeBlockSum, hfirst]
      exact sumSet_mem (hx n (by omega)) (hx (k - (2 * n - 1)) (by omega))
    have hpos : 1 ≤ threeBlockSum x n k := by
      simp [threeBlockSum, hfirst]
      have hnpos := hx_pos n (by omega)
      have hi0 := hx_pos (k - (2 * n - 1)) (by omega)
      omega
    have hlastle : x (k - (2 * n - 1)) ≤ x (n - 1) := by
      by_cases hEq : k - (2 * n - 1) = n - 1
      · simp [hEq]
      · have hlt : k - (2 * n - 1) < n - 1 := by omega
        have hltx := hstrict (by omega) (by omega) hlt
        omega
    have hupper : threeBlockSum x n k ≤ x n + x (n - 1) := by
      simp [threeBlockSum, hfirst]
      omega
    exact ⟨hsum, hpos, hupper⟩

theorem threeBlockSum_strict {x : Nat → Nat} {n : Nat}
    (hn : 2 ≤ n)
    (hstrict : StrictlyIncreasingOn x (n + 1))
    (hgap : 2 * x (n - 1) < x n + x 0) :
    ∀ ⦃i j : Nat⦄, i < 3 * n - 1 → j < 3 * n - 1 → i < j →
      threeBlockSum x n i < threeBlockSum x n j := by
  intro i j hi hj hij
  by_cases hifirst : i < 2 * n - 1
  · by_cases hjfirst : j < 2 * n - 1
    · simp [threeBlockSum, hifirst, hjfirst]
      exact boundarySum_strict hn
        (fun a b ha hb hab => hstrict (by omega) (by omega) hab)
        (by omega) (by omega) hij
    · have hjsecond : 2 * n - 1 ≤ j := by omega
      have hjidx : j - (2 * n - 1) < n := by omega
      have hbound := boundarySum_le_twice_last (x := x) hn
        (fun a b ha hb hab => hstrict (by omega) (by omega) hab) hifirst
      have h0idx : x 0 ≤ x (j - (2 * n - 1)) := by
        by_cases hEq : j - (2 * n - 1) = 0
        · simp [hEq]
        · have hlt : 0 < j - (2 * n - 1) := by omega
          have hltx := hstrict (by omega) (by omega) hlt
          omega
      simp [threeBlockSum, hifirst, hjfirst]
      omega
  · have hisec : 2 * n - 1 ≤ i := by omega
    have hjsec : 2 * n - 1 ≤ j := by omega
    have hiidx : i - (2 * n - 1) < n := by omega
    have hjidx : j - (2 * n - 1) < n := by omega
    have hidx : i - (2 * n - 1) < j - (2 * n - 1) := by omega
    have hlt := hstrict (by omega) (by omega) hidx
    have hjfirst : ¬ j < 2 * n - 1 := by omega
    simp [threeBlockSum, hifirst, hjfirst]
    omega

theorem threeBlock_countPos_sum_lower {A : NatSet} {x : Nat → Nat}
    {n N : Nat}
    (hn : 2 ≤ n)
    (hx : ∀ i, i < n + 1 → A (x i))
    (hx_pos : ∀ i, i < n + 1 → 0 < x i)
    (hx_le : ∀ i, i < n + 1 → x i ≤ N)
    (hstrict : StrictlyIncreasingOn x (n + 1))
    (hgap : 2 * x (n - 1) < x n + x 0) :
    3 * n - 1 ≤ countPos (SumSet A) (x n + x (n - 1)) := by
  apply countPos_ge_of_strict (f := threeBlockSum x n)
  · intro i hi
    have hs := threeBlockSum_mem_truncated hn hx hx_pos hx_le hstrict hgap hi
    exact ⟨hs.1, hs.2.1⟩
  · exact threeBlockSum_strict hn hstrict hgap
  · intro i hi
    have hs := threeBlockSum_mem_truncated hn hx hx_pos hx_le hstrict hgap hi
    exact hs.2.2

theorem boundarySum_injective {x : Nat → Nat} {n : Nat}
    (hn : 2 ≤ n) (hstrict : StrictlyIncreasingOn x n) :
    InjectiveBelow (boundarySum x n) (2 * n - 1) := by
  intro i j hi hj heq
  by_cases hi0 : i < n
  · by_cases hj0 : j < n
    · simp [boundarySum, hi0, hj0] at heq
      have hxy : x i = x j := by omega
      by_cases hEq : i = j
      · exact hEq
      · rcases Nat.lt_or_gt_of_ne hEq with hlt | hgt
        · have hltx := hstrict (by omega) (by omega) hlt
          omega
        · have hgtx := hstrict (by omega) (by omega) hgt
          omega
    · have hjn : n ≤ j := by omega
      have hjidx : j - n + 1 < n := by omega
      have hjidx_pos : 0 < j - n + 1 := by omega
      have hjidx_one : 1 ≤ j - n + 1 := by omega
      have hupper_i : x i ≤ x (n - 1) := by
        by_cases hilast : i = n - 1
        · simp [hilast]
        · have hiltn : i < n - 1 := by omega
          have hltx := hstrict (by omega) (by omega) hiltn
          omega
      have hlower_j : x 1 ≤ x (j - n + 1) := by
        by_cases hjone : j - n + 1 = 1
        · simp [hjone]
        · have hjone' : 1 < j - n + 1 := by omega
          have hltx := hstrict (by omega) hjidx hjone'
          omega
      simp [boundarySum, hi0, hj0] at heq
      have hcross : x 0 + x i < x (j - n + 1) + x (n - 1) := by
        have h01 := hstrict (by omega : 0 < n) (by omega : 1 < n) (by omega : 0 < 1)
        omega
      omega
  · have hin : n ≤ i := by omega
    by_cases hj0 : j < n
    · have hjn : n ≤ i := by omega
      have hiidx : i - n + 1 < n := by omega
      have hiidx_one : 1 ≤ i - n + 1 := by omega
      have hupper_j : x j ≤ x (n - 1) := by
        by_cases hjlast : j = n - 1
        · simp [hjlast]
        · have hjlt : j < n - 1 := by omega
          have hltx := hstrict (by omega) (by omega) hjlt
          omega
      have hlower_i : x 1 ≤ x (i - n + 1) := by
        by_cases hione : i - n + 1 = 1
        · simp [hione]
        · have hione' : 1 < i - n + 1 := by omega
          have hltx := hstrict (by omega) hiidx hione'
          omega
      simp [boundarySum, hi0, hj0] at heq
      have hcross : x 0 + x j < x (i - n + 1) + x (n - 1) := by
        have h01 := hstrict (by omega : 0 < n) (by omega : 1 < n) (by omega : 0 < 1)
        omega
      omega
    · have hjn : n ≤ j := by omega
      have hiidx : i - n + 1 < n := by omega
      have hjidx : j - n + 1 < n := by omega
      simp [boundarySum, hi0, hj0] at heq
      have hxy : x (i - n + 1) = x (j - n + 1) := by omega
      by_cases hEq : i = j
      · exact hEq
      · have hEq' : i - n + 1 ≠ j - n + 1 := by
          intro hidx
          omega
        rcases Nat.lt_or_gt_of_ne hEq' with hlt | hgt
        · have hltx := hstrict hiidx hjidx hlt
          omega
        · have hgtx := hstrict hjidx hiidx hgt
          omega

theorem strictSequence_has_2n_sub_one_sums {A : NatSet} {x : Nat → Nat} {n : Nat}
    (hn : 2 ≤ n) (hx : ∀ i, i < n → A (x i))
    (hstrict : StrictlyIncreasingOn x n) :
    HasDistinctWitnesses (SumSet A) (2 * n - 1) := by
  refine ⟨boundarySum x n, ?_, boundarySum_injective hn hstrict⟩
  intro i hi
  exact boundarySum_mem hx hi

theorem strictSequence_has_truncated_2n_sub_one_sums
    {A : NatSet} {x : Nat → Nat} {n N : Nat}
    (hn : 2 ≤ n)
    (hx : ∀ i, i < n → A (x i))
    (hx_pos : ∀ i, i < n → 0 < x i)
    (hx_le : ∀ i, i < n → x i ≤ N)
    (hstrict : StrictlyIncreasingOn x n) :
    HasDistinctWitnesses (TruncatedSumSet A (2 * N)) (2 * n - 1) := by
  refine ⟨boundarySum x n, ?_, boundarySum_injective hn hstrict⟩
  intro i hi
  exact boundarySum_mem_truncated hx hx_pos hx_le hi

theorem strictSequence_countPos_sum_lower
    {A : NatSet} {x : Nat → Nat} {n N : Nat}
    (hn : 2 ≤ n)
    (hx : ∀ i, i < n → A (x i))
    (hx_pos : ∀ i, i < n → 0 < x i)
    (hx_le : ∀ i, i < n → x i ≤ N)
    (hstrict : StrictlyIncreasingOn x n) :
    2 * n - 1 ≤ countPos (SumSet A) (2 * N) := by
  apply countPos_ge_of_strict (f := boundarySum x n)
  · intro i hi
    have hs := boundarySum_mem_truncated hx hx_pos hx_le hi
    exact ⟨hs.1, hs.2.1⟩
  · exact boundarySum_strict hn hstrict
  · intro i hi
    have hs := boundarySum_mem_truncated hx hx_pos hx_le hi
    exact hs.2.2

theorem infinite_has_truncated_sum_witness {A : NatSet} (hA : Infinite A)
    {n : Nat} (hn : 2 ≤ n) :
    ∃ N : Nat, HasDistinctWitnesses (TruncatedSumSet A (2 * N)) (2 * n - 1) := by
  obtain ⟨x, hx, hpos, hstrict⟩ := infinite_has_increasing_witness hA n
  let N := x (n - 1)
  refine ⟨N, strictSequence_has_truncated_2n_sub_one_sums hn hx hpos ?_ hstrict⟩
  intro i hi
  by_cases hilast : i = n - 1
  · simp [N, hilast]
  · have hilt : i < n - 1 := by omega
    have hlt := hstrict (by omega) (by omega : n - 1 < n) hilt
    simp [N]
    omega

theorem infinite_has_countPos_sum_lower {A : NatSet} (hA : Infinite A)
    {n : Nat} (hn : 2 ≤ n) :
    ∃ N : Nat, 2 * n - 1 ≤ countPos (SumSet A) (2 * N) := by
  obtain ⟨x, hx, hpos, hstrict⟩ := infinite_has_increasing_witness hA n
  let N := x (n - 1)
  refine ⟨N, strictSequence_countPos_sum_lower hn hx hpos ?_ hstrict⟩
  intro i hi
  by_cases hilast : i = n - 1
  · simp [N, hilast]
  · have hilt : i < n - 1 := by omega
    have hlt := hstrict (by omega) (by omega : n - 1 < n) hilt
    simp [N]
    omega

theorem hasDistinctWitnesses_mono {S T : NatSet} {m : Nat}
    (hST : ∀ s, S s → T s) (hS : HasDistinctWitnesses S m) :
    HasDistinctWitnesses T m := by
  rcases hS with ⟨f, hf, hinj⟩
  exact ⟨f, fun i hi => hST (f i) (hf i hi), hinj⟩

theorem canonical_boundary_example {n : Nat} (hn : 2 ≤ n) :
    HasDistinctWitnesses (SumSet (fun _ => True)) (2 * n - 1) := by
  apply strictSequence_has_2n_sub_one_sums (A := fun _ => True)
    (x := fun i => i) hn
  · intro i hi
    trivial
  · intro i j hi hj hlt
    exact hlt

end
end JSP000216
