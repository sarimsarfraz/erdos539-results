/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Defect
import Erdos539.StationaryDefectMonotone
import Erdos539.StationaryOptimizedProfile

namespace Erdos539Geometry
noncomputable section
open scoped Classical

def pg13ProjectionDefect (T : ℕ) (I : Finset (Fin 13)) : ℝ :=
  stationaryEntropyDefect ((pg13Union T).image (fun x (j : I) ↦ x j.val))
    (finitePush (uniformReference (pg13Union T)) (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val)))

def pg13ProjectionProfile (T : ℕ) (I : Finset (Fin 13)) : ℝ :=
  stationaryEnergyProfile ((pg13Union T).image (fun x (j : I) ↦ x j.val))
    (finitePush (uniformReference (pg13Union T)) (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val)))

theorem pg13Union_projection_defect {T : ℕ} (hT : 0 < T) (I : Finset (Fin 13)) :
    pg13ProjectionDefect T I ≤ 2 * Real.log 13 + 7 * Real.log 2 := by
  let φ : (Fin 13 → ℤ) →+ (I → ℤ) :=
    { toFun := fun x j ↦ x j.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hS := pg13Union_nonempty hT
  have h := stationaryEntropyDefect_image_le (fun x ↦ (uniformReference_pos hS x).le)
    (uniformReference_sum hS) φ
  exact h.trans (pg13Union_defect hT)

end
end Erdos539Geometry
