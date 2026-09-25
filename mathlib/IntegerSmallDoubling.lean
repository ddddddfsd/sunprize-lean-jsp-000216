import Mathlib.Combinatorics.Additive.VerySmallDoubling
import Mathlib.GroupTheory.OrderOfElement
import FreimanProgression

open Set
open scoped Pointwise

namespace IntegerSmallDoubling

noncomputable section

/-! ### A finite transfer interface for the `3k - 4` route

The full `3k - 4` inverse theorem is not part of Mathlib.  The lemma below
isolates exactly the numerical consequence needed after such an inverse theorem
has supplied a progression cover: a primitive set's diameter is bounded by the
sumset-cardinality excess.  It is deliberately stated independently of any
unproved structural theorem. -/

lemma primitive_cover_excess_bound
    (F : Finset ℤ) (hF : F.Nonempty)
    {a d : ℤ} {n : ℕ}
    (hd : 0 < d) (hcover : ∀ x ∈ F, x ∈ FreimanProgression.apSegment a d n)
    (hprim : FreimanProgression.PrimitiveAt F (F.min' hF))
    (hLen : n ≤ (F + F).card - F.card + 1) :
    ((F.max' hF - F.min' hF + 1).toNat) ≤ (F + F).card - F.card + 1 := by
  exact (FreimanProgression.primitive_diameter_le_cover_length F hF hd hcover hLen hprim)

lemma primitive_cover_span_bound_int
    (F : Finset ℤ) (hF : F.Nonempty) {a d : ℤ} {n : ℕ}
    (hd : 0 < d) (hcover : ∀ x ∈ F, x ∈ FreimanProgression.apSegment a d n)
    (hprim : FreimanProgression.PrimitiveAt F (F.min' hF))
    (hLen : n ≤ (F + F).card - F.card + 1) :
    F.max' hF - F.min' hF + 1 ≤
      ((F + F).card - F.card + 1 : ℕ) := by
  have hdiam := primitive_cover_excess_bound F hF hd hcover hprim hLen
  have hminmax : F.min' hF ≤ F.max' hF := by
    exact Finset.min'_le F _ (F.max'_mem hF) |>.trans_eq rfl
  have hnonneg : 0 ≤ F.max' hF - F.min' hF + 1 := by omega
  have hcardle : F.card ≤ (F + F).card := by
    have hbase := FreimanProgression.card_add_self_ge_two_card_sub_one F hF
    omega
  have hcast0 :
      ((F.max' hF - F.min' hF + 1).toNat : ℤ) ≤
        ((F + F).card - F.card + 1 : ℤ) := by
    exact_mod_cast hdiam
  have hcast :
      ((F.max' hF - F.min' hF + 1).toNat : ℤ) ≤
      ((F + F).card : ℤ) - (F.card : ℤ) + 1 := hcast0
  rw [Int.toNat_of_nonneg hnonneg] at hcast
  simpa [Nat.cast_sub hcardle, Nat.cast_add, Nat.cast_one] using hcast

def toMul : ℤ ↪ Multiplicative ℤ :=
  ⟨Multiplicative.ofAdd, Multiplicative.ofAdd.injective⟩

def mulImage (F : Finset ℤ) : Finset (Multiplicative ℤ) := F.map toMul

lemma mulImage_card (F : Finset ℤ) : (mulImage F).card = F.card := by
  simp [mulImage]

lemma mulImage_add (F : Finset ℤ) : mulImage (F + F) = mulImage F * mulImage F := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨c, hc, rfl⟩
    rcases Finset.mem_add.mp hc with ⟨a, ha, b, hb, hab⟩
    apply Finset.mem_mul.mpr
    refine ⟨Multiplicative.ofAdd a, ?_, Multiplicative.ofAdd b, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    · exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
    · cases hab
      rfl
  · intro hz
    rcases Finset.mem_mul.mp hz with ⟨u, hu, v, hv, huv⟩
    rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨a + b, Finset.mem_add.mpr ⟨a, ha, b, hb, rfl⟩, ?_⟩
    cases huv
    rfl

lemma subgroup_trivial_of_fintype (H : Subgroup (Multiplicative ℤ))
    [Fintype H] : H = ⊥ := by
  apply Subgroup.eq_bot_iff_forall H |>.2
  intro x hx
  have hpow : (x : Multiplicative ℤ) ^ Fintype.card H = 1 := by
    apply (orderOf_dvd_iff_pow_eq_one).1
    simpa [Nat.card_eq_fintype_card] using H.orderOf_dvd_natCard hx
  have hcardpos : 0 < Fintype.card H := Fintype.card_pos_iff.mpr inferInstance
  exact (pow_eq_one_iff.mp hpow).resolve_right (Nat.ne_of_gt hcardpos)

lemma mulImage_subset_of_cover_trivial
    {F : Finset ℤ} {H : Subgroup (Multiplicative ℤ)} {Z : Finset (Multiplicative ℤ)}
    (hH : H = ⊥) (hcover : (mulImage F : Set (Multiplicative ℤ)) ⊆ (H : Set (Multiplicative ℤ)) * Z) :
    mulImage F ⊆ Z := by
  intro u hu
  have hu' := hcover (by simpa using hu)
  rcases hu' with ⟨h, hh, z, hz, hhz⟩
  have hh0 : h = 1 := by
    rw [hH] at hh
    simpa using hh
  have : u = z := by simpa [hh0] using hhz.symm
  rw [this]
  exact hz

/-- A finite integer set with doubling at most `2 - ε` must be bounded in
cardinality.  This is the integer specialization of Mathlib's finite
small-doubling coset-cover theorem: ℤ has no nontrivial finite subgroups. -/
theorem card_le_of_small_doubling {F : Finset ℤ} {ε : ℝ}
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hF : F.Nonempty)
    (hsmall : ((F + F).card : ℝ) ≤ (2 - ε) * F.card) :
    (F.card : ℝ) ≤ 2 / ε - 1 := by
  let A : Finset (Multiplicative ℤ) := mulImage F
  have hA0 : A.Nonempty := by
    dsimp [A, mulImage]
    exact Finset.map_nonempty.mpr hF
  have hAA : ((A * A).card : ℝ) ≤ (2 - ε) * A.card := by
    rw [show A * A = mulImage (F + F) by simp [A, mulImage_add]]
    simpa [A, mulImage] using hsmall
  obtain ⟨H, hHfin, Z, hHcard, hZcard, hZcover⟩ :=
    Finset.doubling_lt_two hε₀ hε₁ hA0 hAA
  letI : Fintype H := hHfin
  have hH0 : H = ⊥ := subgroup_trivial_of_fintype H
  have hsub : A ⊆ Z := mulImage_subset_of_cover_trivial hH0 hZcover
  have hcard : (A.card : ℝ) ≤ Z.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hAcard : A.card = F.card := by exact mulImage_card F
  rw [hAcard] at hcard
  exact hcard.trans hZcard

#print axioms IntegerSmallDoubling.card_le_of_small_doubling

end
end IntegerSmallDoubling
