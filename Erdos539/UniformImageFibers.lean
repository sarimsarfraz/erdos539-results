/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsImageFibers
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G H : Type*} [DecidableEq H]

theorem uniformReference_image_mass (S : Finset G) (φ : G → H) (y : S.image φ) :
    finitePush (uniformReference S) (imageEndpoint S φ) y =
      (fiber S φ y.val).card / (S.card : ℝ) := by
  rw [finitePush_imageEndpoint_eq_fiber]
  simp only [uniformReference, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one_div]

/-- A uniform law conditions to the uniform law on each literal fiber. -/
theorem uniformReference_imageFiber {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (y : S.image φ) :
    imageFiberReference S φ (uniformReference S) y = uniformReference (fiber S φ y.val) := by
  funext x
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : ((fiber S φ y.val).card : ℝ) ≠ 0 := by
    exact_mod_cast (imageFiber_nonempty S φ y).card_pos.ne'
  simp only [imageFiberReference, uniformReference_image_mass, uniformReference]
  field_simp

/-- Equal-size actual fibers give a uniform image law. -/
theorem uniformReference_image_of_constant_fibers {S : Finset G} (hS : S.Nonempty)
    (φ : G → H) {k : ℕ} (hk : ∀ y : S.image φ, (fiber S φ y.val).card = k)
    (hcard : S.card = (S.image φ).card * k) :
    finitePush (uniformReference S) (imageEndpoint S φ) = uniformReference (S.image φ) := by
  funext y
  have hy := imageFiber_nonempty S φ y
  have hkp : 0 < k := by simpa only [hk y] using hy.card_pos
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hkp.ne'
  have hn : ((S.image φ).card : ℝ) ≠ 0 := by exact_mod_cast (hS.image φ).card_pos.ne'
  rw [uniformReference_image_mass, hk y, hcard]
  simp only [uniformReference, Nat.cast_mul]
  field_simp

end
end Erdos539Geometry
