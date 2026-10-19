/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedBinaryCode

namespace Erdos539Geometry
open scoped Classical
variable {ι : Type*} {m : ℕ} {σ : Fin m → ι → Bool}

theorem signedBinaryCode_coordinate_injective (σ : Fin m → ι → Bool) (i : ι) :
    Function.Injective (fun η ↦ signedBinaryCode m σ η i) := by
  intro η ξ he
  change signedBinaryCode m σ η i = signedBinaryCode m σ ξ i at he
  by_contra hne
  obtain ⟨j, _, hj⟩ := signedBinaryCode_leading m σ η ξ hne
  have hh := hj i
  rw [he, sub_self, zero_mul] at hh
  exact lt_irrefl _ hh

theorem signedBinaryCode_first_leading (i₀ : ι) (hfirst : ∀ j, σ j i₀ = true)
    {η ξ : Fin m → Bool} (hlt : signedBinaryCode m σ η i₀ < signedBinaryCode m σ ξ i₀) :
    ∃ j : Fin m, η j = false ∧ ξ j = true ∧ ∀ i,
      if σ j i then signedBinaryCode m σ η i < signedBinaryCode m σ ξ i
      else signedBinaryCode m σ ξ i < signedBinaryCode m σ η i := by
  have hne : η ≠ ξ := by intro he; subst ξ; exact lt_irrefl _ hlt
  obtain ⟨j, hj, hc⟩ := signedBinaryCode_leading m σ η ξ hne
  have hf := hc i₀
  rw [hfirst j] at hf
  have hb : η j = false ∧ ξ j = true := by
    cases ha : η j <;> cases hb : ξ j <;> simp_all [binaryDigit, binarySign]
    omega
  refine ⟨j, hb.1, hb.2, ?_⟩
  intro i
  have hi := hc i
  rw [hb.1, hb.2] at hi
  cases hs : σ j i <;> simp [hs, binaryDigit, binarySign] at hi ⊢ <;> omega

/-- Distinct successive leading digits give different sign vectors, so a
triple ordered by the first coordinate cannot be coordinatewise between. -/
theorem signedBinaryCode_ordered_no_between (i₀ : ι) (hfirst : ∀ j, σ j i₀ = true)
    (hs : Function.Injective σ) {η ξ ζ : Fin m → Bool}
    (hηξ : signedBinaryCode m σ η i₀ < signedBinaryCode m σ ξ i₀)
    (hξζ : signedBinaryCode m σ ξ i₀ < signedBinaryCode m σ ζ i₀) :
    ¬ ∀ i, min (signedBinaryCode m σ η i) (signedBinaryCode m σ ζ i) ≤ signedBinaryCode m σ ξ i ∧
      signedBinaryCode m σ ξ i ≤ max (signedBinaryCode m σ η i) (signedBinaryCode m σ ζ i) := by
  obtain ⟨j, _hη, hξ, hj⟩ := signedBinaryCode_first_leading i₀ hfirst hηξ
  obtain ⟨k, hξ', _hζ, hk⟩ := signedBinaryCode_first_leading i₀ hfirst hξζ
  have hjk : j ≠ k := by intro he; subst k; simp [hξ] at hξ'
  have hsig : σ j ≠ σ k := fun he ↦ hjk (hs he)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hsig
  intro hbox
  have hbi := hbox i
  have hji := hj i
  have hki := hk i
  cases hjb : σ j i <;> cases hkb : σ k i <;>
    simp only [hjb, hkb, Bool.false_eq_true, ite_false, ite_true] at hi hji hki
  all_goals try contradiction
  all_goals simp only [min_def, max_def] at hbi; split_ifs at hbi <;> omega

theorem signedBinaryCode_no_between (i₀ : ι) (hfirst : ∀ j, σ j i₀ = true)
    (hs : Function.Injective σ) {η ξ ζ : Fin m → Bool} (hηξ : η ≠ ξ) (hξζ : ξ ≠ ζ) :
    ¬ ∀ i, min (signedBinaryCode m σ η i) (signedBinaryCode m σ ζ i) ≤ signedBinaryCode m σ ξ i ∧
      signedBinaryCode m σ ξ i ≤ max (signedBinaryCode m σ η i) (signedBinaryCode m σ ζ i) := by
  intro hbox
  have hab := (signedBinaryCode_coordinate_injective σ i₀).ne hηξ
  have hbc := (signedBinaryCode_coordinate_injective σ i₀).ne hξζ
  rcases lt_or_gt_of_ne hab with h | h
  · have hbc' : signedBinaryCode m σ ξ i₀ < signedBinaryCode m σ ζ i₀ := by
      rcases le_max_iff.mp (hbox i₀).2 with hh | hh <;> omega
    exact signedBinaryCode_ordered_no_between i₀ hfirst hs h hbc' hbox
  · have hcb : signedBinaryCode m σ ζ i₀ < signedBinaryCode m σ ξ i₀ := by
      rcases min_le_iff.mp (hbox i₀).1 with hh | hh <;> omega
    apply signedBinaryCode_ordered_no_between i₀ hfirst hs hcb h
    intro i
    simpa only [min_comm, max_comm] using hbox i

end Erdos539Geometry
