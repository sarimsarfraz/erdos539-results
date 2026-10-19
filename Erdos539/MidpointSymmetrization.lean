/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MidpointClosure

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

/-- A midpoint-closed finite set has a symmetric core around an actual point
retaining at least 2^(-rank) of its points. All equal-residue pairs are counted. -/
theorem exists_large_symmetricCore {F : Finset M} (hFn : F.Nonempty)
    (hF : GroupMidpointClosed F) :
    ∃ a ∈ F, F.card ≤ 2 ^ Module.finrank ℤ M * (symmetricCore F a).card := by
  classical
  let e := (Module.finBasis ℤ M).equivFun
  let color := latticeColor e 2
  let P := samePairs F color
  have hP : P.Nonempty := by
    obtain ⟨x, hx⟩ := hFn
    exact ⟨(x, x), mem_samePairs.mpr ⟨hx, hx, rfl⟩⟩
  have hcolors : (F.image color).card ≤ 2 ^ Module.finrank ℤ M := by
    have h := Finset.card_le_univ (F.image color)
    simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card] using h
  have hpairs : F.card ^ 2 ≤ 2 ^ Module.finrank ℤ M * P.card :=
    (card_sq_le_image_mul_samePairs F color).trans (Nat.mul_le_mul_right _ hcolors)
  have hex (p : {p // p ∈ P}) : ∃ a : M, p.val.1 + p.val.2 = (2 : ℤ) • a := by
    obtain ⟨z, hz⟩ := latticeColor_eq_divisible e (mem_samePairs.mp p.property).2.2
    norm_num only [Nat.cast_ofNat] at hz
    refine ⟨z + p.val.2, ?_⟩
    rw [smul_add, ← hz, two_zsmul]
    abel
  let g : {p // p ∈ P} → M := fun p ↦ Classical.choose (hex p)
  have hg (p : {p // p ∈ P}) : p.val.1 + p.val.2 = (2 : ℤ) • g p :=
    Classical.choose_spec (hex p)
  have hgF (p : {p // p ∈ P}) : g p ∈ F :=
    hF _ (mem_samePairs.mp p.property).1 _ (mem_samePairs.mp p.property).2.1 _ (hg p)
  have hPa : P.attach.Nonempty := by simpa only [Finset.attach_nonempty_iff] using hP
  obtain ⟨p0, _hp0, hlarge⟩ := exists_large_fiber P.attach hPa g
  let a := g p0
  let H := fiber P.attach g a
  have himage : P.attach.image g ⊆ F := by
    intro x hx
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hx
    exact hgF p
  have hPc : P.card ≤ F.card * H.card := by
    rw [Finset.card_attach] at hlarge
    exact hlarge.trans (Nat.mul_le_mul_right _ (Finset.card_le_card himage))
  have hH : F.card ≤ 2 ^ Module.finrank ℤ M * H.card := by
    have htot := hpairs.trans (Nat.mul_le_mul_left (2 ^ Module.finrank ℤ M) hPc)
    have hn := hFn.card_pos
    nlinarith
  have hcore : H.card ≤ (symmetricCore F a).card := by
    apply Finset.card_le_card_of_injOn (fun p : {p // p ∈ P} ↦ p.val.1)
    · intro p hp
      have hpa := (mem_fiber.mp hp).2
      have hsum := hg p
      rw [hpa] at hsum
      apply mem_symmetricCore.mpr
      refine ⟨(mem_samePairs.mp p.property).1, ?_⟩
      have he : (2 : ℤ) • a - p.val.1 = p.val.2 := by rw [← hsum]; abel
      rw [he]
      exact (mem_samePairs.mp p.property).2.1
    · intro p hp q hq hpq
      change p.val.1 = q.val.1 at hpq
      apply Subtype.ext
      apply Prod.ext hpq
      have hp' := hg p
      have hq' := hg q
      rw [(mem_fiber.mp hp).2] at hp'
      rw [(mem_fiber.mp hq).2] at hq'
      rw [hpq] at hp'
      exact add_left_cancel (hp'.trans hq'.symm)
  exact ⟨a, hgF p0, hH.trans (Nat.mul_le_mul_left _ hcore)⟩

end
end Erdos539Geometry
