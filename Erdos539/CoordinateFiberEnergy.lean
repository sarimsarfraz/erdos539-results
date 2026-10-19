/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PushWeight
import Erdos539.FiberEnergy
import Erdos539.SliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateFiberEnergyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The actual two-block coordinate map, with the conditioned block second. -/
def coordinateSplit (I J : Finset ι) : (ι → ℝ) →+ ((J → ℝ) × (I → ℝ)) where
  toFun := fun x ↦ (project J x, project I x)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coordinateSplit_injective (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J) :
    Function.Injective (coordinateSplit I J) := by
  intro x y hxy
  funext i
  rcases hcover i with hi | hj
  · exact congrFun (congrArg Prod.snd hxy) ⟨i, hi⟩
  · exact congrFun (congrArg Prod.fst hxy) ⟨i, hj⟩

theorem rowSupport_coordinateSplit (B : Finset (ι → ℝ)) (I J : Finset ι) (v : I → ℝ) :
    rowSupport (B.image (coordinateSplit I J)) v = projection (fiber B (project I) v) J := by
  ext u
  simp only [mem_rowSupport, Finset.mem_image, projection, mem_fiber, coordinateSplit,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, hxu, hxv⟩
    exact ⟨x, ⟨hx, hxv⟩, hxu⟩
  · rintro ⟨x, ⟨hx, hxv⟩, hxu⟩
    exact ⟨x, hx, hxu, hxv⟩

/-- Square-root marginal weights, calculated on the actual two-block
coordinate image of the parent. -/
def coordinateMarginalWeight (A : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ)
    (I J : Finset ι) : (I → ℝ) → ℝ :=
  rowNormWeight (projection A J) (pushWeight A (coordinateSplit I J) w)

def coordinateMarginalEnergy (A : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ)
    (I J : Finset ι) : ℝ :=
  weightedEnergy (projection A I) (coordinateMarginalWeight A w I J)

/-- Restricting the original weight to a subset decreases its actual
square-root marginal energy. The parent row and column alphabets stay fixed. -/
theorem coordinateMarginalEnergy_restricted_le {A B : Finset (ι → ℝ)} (hBA : B ⊆ A)
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ A, 0 ≤ w x) (I J : Finset ι) :
    weightedEnergy (projection A I)
      (rowNormWeight (projection A J) (pushWeight B (coordinateSplit I J) w)) ≤
      coordinateMarginalEnergy A w I J := by
  apply weightedEnergy_mono
  · intro v _
    exact rowNormWeight_nonneg _ _ _
  · intro v _
    exact rowNormWeight_mono _ v
      (fun u _ ↦ pushWeight_nonneg (fun x hx ↦ hw x (hBA hx)) (u,v))
      (fun u _ ↦ pushWeight_mono hBA (coordinateSplit I J) hw (u,v))

/-- Fiber control for a subset uses the same original parent's marginal
energy. The subset's own marginals are not substituted into the conclusion. -/
theorem coordinate_fiber_energy_bound {A B : Finset (ι → ℝ)} (hBA : B ⊆ A)
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ A, 0 ≤ w x)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J) {M : ℝ} (hM : 0 ≤ M)
    (hrows : ∀ v ∈ projection A I, energyNorm (projection (fiber B (project I) v) J) ≤ M) :
    weightedEnergy B w ≤ M * coordinateMarginalEnergy A w I J := by
  let φ := coordinateSplit I J
  let R := B.image φ
  have hR : R ⊆ projection A J ×ˢ projection A I := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    constructor <;> simp only [projection, Finset.mem_image]
    · exact ⟨x, hBA hx, rfl⟩
    · exact ⟨x, hBA hx, rfl⟩
  have hz : ∀ p ∈ projection A J ×ˢ projection A I, p ∉ R → pushWeight B φ w p = 0 := by
    intro p _ hp
    exact pushWeight_zero w hp
  have hr : ∀ v ∈ projection A I, energyNorm (rowSupport R v) ≤ M := by
    intro v hv
    rw [show R = B.image (coordinateSplit I J) from rfl, rowSupport_coordinateSplit]
    exact hrows v hv
  have h := weightedEnergy_relation_le_marginal hR (pushWeight B φ w) hz hM hr
  rw [weightedEnergy_pushWeight B φ (coordinateSplit_injective I J hcover)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (coordinateMarginalEnergy_restricted_le hBA w hw I J) hM)

end
end Erdos539Geometry
