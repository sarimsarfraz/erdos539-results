/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fibers

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

/-- The coordinate fiber of `a`, retaining the original ambient coordinates. -/
def slice (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) : Finset (ι → ℝ) :=
  fiber F (project I) (project I a)

def restrictedFan (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) : Finset (ι → ℝ) :=
  fan (slice F I a) a

/-- The maximum of individual same-fiber fans, not a union over anchors. -/
def maxRestrictedFan (F : Finset (ι → ℝ)) (I : Finset ι) : ℕ :=
  F.sup (fun a ↦ (restrictedFan F I a).card)

@[simp] theorem mem_slice {F : Finset (ι → ℝ)} {I : Finset ι} {a x : ι → ℝ} :
    x ∈ slice F I a ↔ x ∈ F ∧ project I x = project I a := mem_fiber

theorem slice_subset (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) :
    slice F I a ⊆ F := fun _ hx ↦ (mem_slice.mp hx).1

theorem slice_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) (I : Finset ι) (a : ι → ℝ) :
    slice F I a ⊆ slice G I a := by
  intro x hx
  exact mem_slice.mpr ⟨h (mem_slice.mp hx).1, (mem_slice.mp hx).2⟩

theorem restrictedFan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G)
    (I : Finset ι) (a : ι → ℝ) :
    restrictedFan F I a ⊆ restrictedFan G I a := fan_mono (slice_mono h I a) a

theorem card_restrictedFan_le_max {F : Finset (ι → ℝ)} (I : Finset ι)
    {a : ι → ℝ} (ha : a ∈ F) :
    (restrictedFan F I a).card ≤ maxRestrictedFan F I :=
  Finset.le_sup (f := fun a ↦ (restrictedFan F I a).card) ha

theorem maxRestrictedFan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) (I : Finset ι) :
    maxRestrictedFan F I ≤ maxRestrictedFan G I := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.card_le_card (restrictedFan_mono h I a)).trans
    (card_restrictedFan_le_max I (h ha))

theorem maxRestrictedFan_le_maxFan (F : Finset (ι → ℝ)) (I : Finset ι) :
    maxRestrictedFan F I ≤ maxFan F := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.card_le_card (fan_mono (slice_subset F I a) a)).trans (card_fan_le_maxFan ha)

theorem one_le_maxRestrictedFan {F : Finset (ι → ℝ)} (hF : F.Nonempty) (I : Finset ι) :
    1 ≤ maxRestrictedFan F I := by
  obtain ⟨a, ha⟩ := hF
  have ha' : a ∈ slice F I a := mem_slice.mpr ⟨ha, rfl⟩
  have hz : (0 : ι → ℝ) ∈ restrictedFan F I a := mem_fan.mpr ⟨a, ha', pdiff_self a⟩
  exact (Finset.card_pos.mpr ⟨0, hz⟩).trans_le (card_restrictedFan_le_max I ha)

theorem exists_restrictedFan_ge {F : Finset (ι → ℝ)} {I : Finset ι}
    {k : ℕ} (hk : 0 < k) (h : k ≤ maxRestrictedFan F I) :
    ∃ a ∈ F, k ≤ (restrictedFan F I a).card := by
  by_contra hn
  push_neg at hn
  have hb : maxRestrictedFan F I ≤ k - 1 := by
    apply Finset.sup_le
    intro a ha
    have hh := hn a ha
    omega
  omega

@[simp] theorem slice_empty (F : Finset (ι → ℝ)) (a : ι → ℝ) : slice F ∅ a = F := by
  ext x
  simp only [mem_slice, and_iff_left_iff_imp]
  intro _
  funext i
  exact False.elim (Finset.notMem_empty i.val i.property)

@[simp] theorem maxRestrictedFan_empty (F : Finset (ι → ℝ)) :
    maxRestrictedFan F ∅ = maxFan F := by
  simp only [maxRestrictedFan, restrictedFan, slice_empty, maxFan]

theorem restrictedFan_zero_on {F : Finset (ι → ℝ)} {I : Finset ι}
    {a z : ι → ℝ} (hz : z ∈ restrictedFan F I a) (i : ι) (hi : i ∈ I) : z i = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_fan.mp hz
  have he := congrFun (mem_slice.mp hx).2 ⟨i, hi⟩
  change x i = a i at he
  simp [pdiff, he]

end
end Erdos539Geometry
