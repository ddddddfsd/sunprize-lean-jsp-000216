import Mathlib

/-!
# Exact bridge for Erdős Problem 245

This module connects the finite reciprocal-error inequality used by the
additive-combinatorics core to the exact `Set`/`Filter`/`EReal` statement in
`FormalConjectures.ErdosProblems.245`.  The finite-to-infinite theorem that
produces `SetApprox` from zero density is intentionally supplied by callers.
-/

open Filter Set
open scoped Pointwise Topology

noncomputable section

namespace Erdos245Bridge2

lemma trunc_finite (A : Set ℕ) (N : ℕ) :
    (A ∩ Icc 1 N).Finite := by
  exact (finite_Icc 1 N).subset inter_subset_right

lemma sum_trunc_finite (A : Set ℕ) (N : ℕ) :
    ((A + A) ∩ Icc 1 N).Finite := by
  exact (finite_Icc 1 N).subset inter_subset_right

lemma trunc_pos_eventually (A : Set ℕ) (hA : A.Infinite) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < (A ∩ Icc 1 N).ncard := by
  obtain ⟨a, haA, ha_gt⟩ := hA.exists_gt 0
  refine ⟨a, ?_⟩
  intro N hN
  apply (Set.ncard_pos (trunc_finite A N)).2
  refine ⟨a, haA, ?_⟩
  exact ⟨by omega, hN⟩

def ratio (A : Set ℕ) (x : ℝ) : EReal :=
  (((A + A) ∩ Icc 1 ⌊x⌋₊).ncard : EReal) /
    ((A ∩ Icc 1 ⌊x⌋₊).ncard : EReal)

lemma ratio_eq_catalogue (A : Set ℕ) :
    ratio A = fun N : ℝ =>
      ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
        (A ∩ Icc 1 ⌊N⌋₊).ncard := rfl

def SetApprox (A : Set ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
    (3 * k - 1) * (A ∩ Icc 1 N).ncard ≤
      k * ((A + A) ∩ Icc 1 N).ncard

/- A generic transport lemma isolates the only bookkeeping needed when a
core-Lean counting function is connected to `Set.ncard`.  The substantive
inequality remains entirely in the caller's discrete hypothesis. -/
lemma discrete_count_transport {A : Set ℕ} {c d : ℕ → ℕ}
    (hc : ∀ N : ℕ, c N = (A ∩ Icc 1 N).ncard)
    (hd : ∀ N : ℕ, d N = ((A + A) ∩ Icc 1 N).ncard)
    (h : ∀ k : ℕ, 0 < k → ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (3 * k - 1) * c N ≤ k * d N) :
    SetApprox A := by
  intro k hk M
  obtain ⟨N, hMN, hN⟩ := h k hk M
  refine ⟨N, hMN, ?_⟩
  simpa [hc N, hd N] using hN

lemma cast_ratio_lower_bound {a b k : ℕ} (hk : 0 < k) (ha : 0 < a)
    (h : (3 * k - 1) * a ≤ k * b) :
    ((3 : ℝ) - 1 / (k : ℝ) : EReal) ≤ (b : EReal) / (a : EReal) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcast : ((3 * k - 1 : ℕ) : ℝ) * (a : ℝ) ≤
      (k : ℝ) * (b : ℝ) := by exact_mod_cast h
  have hcast_sub : ((3 * k - 1 : ℕ) : ℝ) = 3 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hmul : (k : ℝ) * ((3 - 1 / (k : ℝ)) * (a : ℝ)) ≤
      (k : ℝ) * (b : ℝ) := by
    rw [hcast_sub] at hcast
    calc
      (k : ℝ) * ((3 - 1 / (k : ℝ)) * (a : ℝ)) =
          (3 * (k : ℝ) - 1) * (a : ℝ) := by
            field_simp
      _ ≤ (k : ℝ) * (b : ℝ) := hcast
  have hreal : (3 - 1 / (k : ℝ)) * (a : ℝ) ≤ (b : ℝ) :=
    le_of_mul_le_mul_left hmul hkR
  have hrealE0 : ((3 : ℝ) - 1 / (k : ℝ)) * (a : ℝ) ≤ (b : ℝ) := hreal
  have hcoefE : (((3 : ℝ) - 1 / (k : ℝ) : ℝ) : EReal) =
      ((3 : ℝ) : EReal) - 1 / (k : EReal) := by
    rw [EReal.coe_sub, EReal.coe_div]
    norm_num
  have hrealE : (((3 : ℝ) - 1 / (k : ℝ) : ℝ) : EReal) * (a : EReal) ≤ (b : EReal) := by
    have hc := EReal.coe_le_coe hrealE0
    simpa [EReal.coe_mul] using hc
  have haE : (0 : EReal) < (a : EReal) := by exact_mod_cast ha
  have hkE : ((k : ℝ) : EReal) = (k : EReal) := EReal.coe_natCast
  have hkinvE : (((k : ℝ)⁻¹ : ℝ) : EReal) = (k : EReal)⁻¹ := EReal.coe_inv _
  have hgoal : (((3 : ℝ) : EReal) - 1 / (k : EReal)) * (a : EReal) ≤ (b : EReal) := by
    simpa [hcoefE, hkE, hkinvE] using hrealE
  change (((3 : EReal) - 1 / (k : EReal)) ≤ (b : EReal) / (a : EReal))
  have hgoal' : ((3 : EReal) - 1 / (k : EReal)) * (a : EReal) ≤ (b : EReal) := hgoal
  exact (EReal.le_div_iff_mul_le haE (EReal.coe_ne_top _)).2 hgoal'

/-- The discrete reciprocal-error inequalities imply the exact EReal limsup lower bound. -/
theorem setApprox_implies_limsup (A : Set ℕ) (hA : A.Infinite)
    (hApprox : SetApprox A) :
    (3 : EReal) ≤ atTop.limsup (ratio A) := by
  apply (Filter.le_limsup_iff).2
  intro y hy
  obtain ⟨r : ℝ, hyr, hr⟩ := EReal.exists_between_coe_real hy
  have hr' : r < (3 : ℝ) := EReal.coe_lt_coe_iff.mp hr
  have hε : 0 < (3 : ℝ) - r := by linarith
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let q : ℕ := k + 1
  have hq : 0 < q := by dsimp [q]; omega
  have hqrat : 1 / (q : ℝ) < (3 : ℝ) - r := by
    simpa [q, Nat.cast_add, Nat.cast_one] using hk
  have hryq : r < (3 : ℝ) - 1 / (q : ℝ) := by linarith
  obtain ⟨N₀, hN₀⟩ := trunc_pos_eventually A hA
  apply frequently_atTop.2
  intro R
  let M : ℕ := max N₀ ⌈R⌉₊
  obtain ⟨N, hMN, hNapprox⟩ := hApprox q hq M
  have hN0 : N₀ ≤ N := le_trans (Nat.le_max_left _ _) hMN
  have hden : 0 < (A ∩ Icc 1 N).ncard := hN₀ N hN0
  have hceilN : ⌈R⌉₊ ≤ N := le_trans (Nat.le_max_right _ _) hMN
  have hRN : R ≤ (N : ℝ) := le_trans (Nat.le_ceil R) (by exact_mod_cast hceilN)
  refine ⟨(N : ℝ), hRN, ?_⟩
  have hlow : ((3 : ℝ) - 1 / (q : ℝ) : EReal) ≤
      ((A + A) ∩ Icc 1 N).ncard / (A ∩ Icc 1 N).ncard := by
    exact cast_ratio_lower_bound hq hden hNapprox
  have hyrE : (y : EReal) < ((3 : ℝ) - 1 / (q : ℝ) : EReal) :=
    lt_of_lt_of_le hyr (EReal.coe_le_coe (le_of_lt hryq))
  exact lt_of_lt_of_le hyrE (by simpa [ratio, Nat.floor_natCast] using hlow)

/- Once the finite additive-combinatorics part has produced `SetApprox` from the
zero-density hypothesis, the exact right-hand side of FormalConjectures' Erdos
245 declaration follows directly.  The density premise is kept at its exact
`Set`/`Filter` type here; no replacement by a Nat-valued surrogate is made. -/
theorem allApprox_implies_erdos_rhs
    (hAll : ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N : ℝ => (A ∩ Icc 1 ⌊N⌋₊).ncard / N) (𝓝 0) → SetApprox A) :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N : ℝ => ((A ∩ Icc 1 ⌊N⌋₊).ncard : ℝ) / N) (𝓝 0) →
      (3 : EReal) ≤ atTop.limsup (ratio A) := by
  intro A hA hzero
  exact setApprox_implies_limsup A hA (hAll A hA hzero)

/- The same implication with the ratio expanded exactly as in the catalogue
statement.  This is the final shape consumed by `Erdos245.erdos_245`. -/
theorem allApprox_implies_catalogue_rhs
    (hAll : ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N : ℝ => (A ∩ Icc 1 ⌊N⌋₊).ncard / N) (𝓝 0) → SetApprox A) :
    ∀ (A : Set ℕ), A.Infinite →
      atTop.Tendsto
        (fun N : ℝ => ((A ∩ Icc 1 ⌊N⌋₊).ncard : ℝ) / N) (𝓝 0) →
      (3 : EReal) ≤ atTop.limsup
        (fun N : ℝ => ((A + A) ∩ Icc 1 ⌊N⌋₊ |>.ncard : EReal) /
          (A ∩ Icc 1 ⌊N⌋₊).ncard) := by
  intro A hA hzero
  change (3 : EReal) ≤ atTop.limsup (ratio A)
  exact allApprox_implies_erdos_rhs hAll A hA hzero

end Erdos245Bridge2


