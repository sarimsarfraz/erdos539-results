/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MidpointDescendants

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- A fiber lying in a coset of a supported subgroup forces a large actual
midpoint descendant. The loss is exactly 4 to the subgroup's rank. -/
theorem midpointDescendant_card_from_coset {F E : Finset M}
    (hF : GroupMidpointClosed F) (hsym : GroupSymmetric F) (hEF : E ⊆ F) (hE : E.Nonempty)
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I : Finset ι) (z0 : M)
    (hcoset : ∀ x ∈ E, x - z0 ∈ latticeSupported e I) :
    E.card ≤ 4 ^ Module.finrank ℤ (latticeSupported e I) * (midpointDescendant F e he I).card := by
  classical
  let K := latticeSupported e I
  let lift : {x // x ∈ E} → K := fun x ↦ ⟨x.val - z0, hcoset x.val x.property⟩
  let C := E.attach.image lift
  have hlift : Function.Injective lift := by
    intro x y h
    apply Subtype.ext
    have hh : x.val - z0 = y.val - z0 := congrArg Subtype.val h
    exact sub_left_injective hh
  have hCcard : C.card = E.card := by
    rw [Finset.card_image_of_injective _ hlift, Finset.card_attach]
  have hC : C.Nonempty := by
    obtain ⟨x, hx⟩ := hE
    exact ⟨lift ⟨x, hx⟩, Finset.mem_image_of_mem lift (Finset.mem_attach E ⟨x, hx⟩)⟩
  obtain ⟨W, hWC, hW, hlarge, hcongr⟩ := exists_large_free_congruence_class (m := 4) hC
  obtain ⟨w0, hw0⟩ := hW
  let g : {w // w ∈ W} → K := fun w ↦ Classical.choose (hcongr w.val w.property w0 hw0)
  have hg (w : {w // w ∈ W}) : w.val - w0 = (4 : ℤ) • g w :=
    Classical.choose_spec (hcongr w.val w.property w0 hw0)
  obtain ⟨x0, _hx0, hx0eq⟩ := Finset.mem_image.mp (hWC hw0)
  have hmem (w : {w // w ∈ W}) : g w ∈ midpointDescendant F e he I := by
    obtain ⟨x, _hx, hxeq⟩ := Finset.mem_image.mp (hWC w.property)
    have hdiff : x.val - x0.val = (4 : ℤ) • (g w).val := by
      have hh := congrArg (fun z : K ↦ z.val) (hg w)
      rw [← hxeq, ← hx0eq] at hh
      change (x.val - z0) - (x0.val - z0) = (4 : ℤ) • (g w).val at hh
      calc
        _ = (x.val - z0) - (x0.val - z0) := by abel
        _ = _ := hh
    apply mem_midpointDescendant.mpr
    apply hF x.val (hEF x.property) (-x0.val) (hsym x0.val (hEF x0.property)) ((2 : ℤ) • (g w).val)
    calc
      _ = x.val - x0.val := (sub_eq_add_neg _ _).symm
      _ = (4 : ℤ) • (g w).val := hdiff
      _ = _ := by rw [smul_smul]; norm_num
  have hinj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have hh : x.val - w0 = y.val - w0 := by rw [hg x, hg y, hxy]
    exact sub_left_injective hh
  have hWcard : W.card ≤ (midpointDescendant F e he I).card := by
    have hc : W.attach.card = W.card := Finset.card_attach
    rw [← hc]
    exact Finset.card_le_card_of_injOn g (fun w _ ↦ hmem w) hinj.injOn
  rw [hCcard] at hlarge
  exact hlarge.trans (Nat.mul_le_mul_left _ hWcard)

end
end Erdos539Geometry
