import Mathlib

open Set Finset

namespace FreimanProgression

/-- The finite arithmetic progression with initial term `a`, positive step `d`,
    and `n` terms. -/
def apSegment (a d : ℤ) (n : ℕ) : Set ℤ :=
  (fun i : ℕ => a + d * (i : ℤ)) '' Set.Iio n

/-- A set is covered by a progression whose number of terms is at most `L`. -/
def progressionCoverLengthAtMost (A : Set ℤ) (L : ℕ) : Prop :=
  ∃ a d : ℤ, ∃ n : ℕ, 0 < d ∧ A ⊆ apSegment a d n ∧ n ≤ L

lemma mem_apSegment_one {a x : ℤ} {n : ℕ}
    (hax : a ≤ x) (hxn : x < a + n) : x ∈ apSegment a 1 n := by
  have hdiff : 0 ≤ x - a := sub_nonneg.mpr hax
  have hlt : x - a < (n : ℤ) := by omega
  have hnpos : n ≠ 0 := by omega
  have hnat : (x - a).toNat < n := by
    rw [Int.toNat_lt_of_ne_zero hnpos]
    exact hlt
  refine ⟨(x - a).toNat, hnat, ?_⟩
  simp [Int.toNat_of_nonneg hdiff]

/-- Finite diameter bound implies a progression cover.  This is the
    diameter-to-progression part of the finite Freiman route: after translating
    the minimum to zero, the unit-step progression through the maximum covers
    the set, with exactly the diameter many terms. -/
theorem finset_progression_cover_of_diameter
    (F : Finset ℤ) (hF : F.Nonempty) {L : ℕ}
    (hdiam : ((F.max' hF - F.min' hF + 1).toNat) ≤ L) :
    ∃ a d : ℤ, ∃ n : ℕ,
      0 < d ∧ (∀ x ∈ F, x ∈ apSegment a d n) ∧ n ≤ L := by
  let lo : ℤ := F.min' hF
  let hi : ℤ := F.max' hF
  let n : ℕ := (hi - lo + 1).toNat
  have hlo_mem : lo ∈ F := by
    exact Finset.min'_mem F hF
  have hhi_mem : hi ∈ F := by
    exact Finset.max'_mem F hF
  have hlohi : lo ≤ hi := by
    exact Finset.min'_le F hi hhi_mem |>.trans_eq (by rfl)
  have hnpos : n ≠ 0 := by
    dsimp [n]
    rw [Int.toNat_eq_zero]
    omega
  have hcover : ∀ x ∈ F, x ∈ apSegment lo 1 n := by
    intro x hx
    have hxlo : lo ≤ x := by
      exact Finset.min'_le F x hx
    have hxhi : x ≤ hi := by
      exact Finset.le_max' F x hx
    apply mem_apSegment_one hxlo
    dsimp [n]
    rw [Int.ofNat_toNat]
    omega
  refine ⟨lo, 1, n, by norm_num, hcover, ?_⟩
  simpa [lo, hi, n] using hdiam

/-- Set form of the diameter cover, obtained by passing to its finite support. -/
theorem finite_set_progression_cover_of_diameter
    {A : Set ℤ} (hA : A.Finite) (hA0 : A.Nonempty) {L : ℕ}
    (hdiam : ((hA.toFinset.max' (hA.toFinset_nonempty.mpr hA0) -
      hA.toFinset.min' (hA.toFinset_nonempty.mpr hA0) + 1).toNat) ≤ L) :
    progressionCoverLengthAtMost A L := by
  let F := hA.toFinset
  have hF : F.Nonempty := hA.toFinset_nonempty.mpr hA0
  obtain ⟨a, d, n, hd, hcover, hn⟩ :=
    finset_progression_cover_of_diameter F hF (by simpa [F] using hdiam)
  refine ⟨a, d, n, hd, ?_, hn⟩
  intro x hx
  exact hcover x (by simpa [F] using hx)

/- A primitive finite set has no nontrivial common positive divisor in its
   differences.  This formulation avoids depending on a particular gcd API
   and is convenient when a progression cover is obtained from Freiman's
   structural theorem. -/
def PrimitiveAt (F : Finset ℤ) (x₀ : ℤ) : Prop :=
  x₀ ∈ F ∧ ∀ d : ℤ, 0 < d → (∀ x ∈ F, d ∣ x - x₀) → d = 1

lemma progression_step_eq_one_of_primitive
    (F : Finset ℤ) (hF : F.Nonempty) {a d : ℤ} {n : ℕ}
    (hd : 0 < d) (hcover : ∀ x ∈ F, x ∈ apSegment a d n)
    (hprim : PrimitiveAt F (F.min' hF)) :
    d = 1 := by
  apply hprim.2 d hd
  obtain ⟨i₀, hi₀, hmin⟩ := hcover _ (F.min'_mem hF)
  intro x hx
  rcases hcover x hx with ⟨i, hi, hi_eq⟩
  simp only [apSegment] at hmin hi_eq
  subst x
  rw [← hmin]
  exact ⟨(i : ℤ) - i₀, by ring⟩

lemma primitive_diameter_le_cover_length
    (F : Finset ℤ) (hF : F.Nonempty) {L : ℕ}
    {a d : ℤ} {n : ℕ}
    (hd : 0 < d) (hcover : ∀ x ∈ F, x ∈ apSegment a d n)
    (hn : n ≤ L) (hprim : PrimitiveAt F (F.min' hF)) :
    ((F.max' hF - F.min' hF + 1).toNat) ≤ L := by
  have hd1 : d = 1 := progression_step_eq_one_of_primitive F hF hd hcover hprim
  subst hd1
  have hmin : F.min' hF ∈ apSegment a 1 n := hcover _ (F.min'_mem hF)
  have hmax : F.max' hF ∈ apSegment a 1 n := hcover _ (F.max'_mem hF)
  rcases hmin with ⟨i, hi, hmin_eq⟩
  rcases hmax with ⟨j, hj, hmax_eq⟩
  simp only [apSegment] at hmin_eq hmax_eq
  have hdiff : F.max' hF - F.min' hF = (j : ℤ) - i := by omega
  have hnonneg : 0 ≤ (j : ℤ) - i := by
    have hminmax : F.min' hF ≤ F.max' hF :=
      Finset.min'_le F _ (F.max'_mem hF) |>.trans_eq rfl
    omega
  have hijZ : (i : ℤ) ≤ j := by omega
  have hij : i ≤ j := by exact_mod_cast hijZ
  have hnat : (F.max' hF - F.min' hF + 1).toNat ≤ n := by
    have hpos : 0 ≤ F.max' hF - F.min' hF + 1 := by omega
    have hj' : j < n := hj
    have hle : F.max' hF - F.min' hF + 1 ≤ (n : ℤ) := by
      rw [hdiff]
      omega
    have hle' : ((F.max' hF - F.min' hF + 1).toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
      exact hle
    exact_mod_cast hle'
  exact hnat.trans hn

end FreimanProgression

#print axioms FreimanProgression.finset_progression_cover_of_diameter
#print axioms FreimanProgression.finite_set_progression_cover_of_diameter
#print axioms FreimanProgression.progression_step_eq_one_of_primitive
#print axioms FreimanProgression.primitive_diameter_le_cover_length

