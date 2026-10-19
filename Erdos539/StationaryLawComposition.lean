/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryProjectionProfile

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H K : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup K]

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem entropy_eq_finiteEntropy_flat (Q : StationaryAdditiveLaw S ν) :
    Q.entropy = finiteEntropy Q.flat := by
  simp only [entropy, finiteEntropy, flat, Fintype.sum_prod_type]

theorem flat_map (Q : StationaryAdditiveLaw S ν) {T : Finset H} (e : S → T)
    (hrel : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val) :
    (Q.map e hrel).flat = finitePush Q.flat (mapFour e) := rfl

/-- Two successive pushforwards preserve the same root-referenced
correlation as the composed endpoint map. -/
theorem correlation_map_comp (Q : StationaryAdditiveLaw S ν)
    {T : Finset H} {U : Finset K} (e : S → T) (g : T → U)
    (he : ∀ a b c d : S, a.val + b.val = c.val + d.val →
      (e a).val + (e b).val = (e c).val + (e d).val)
    (hg : ∀ a b c d : T, a.val + b.val = c.val + d.val →
      (g a).val + (g b).val = (g c).val + (g d).val) :
    ((Q.map e he).map g hg).correlation =
      (Q.map (g ∘ e) (fun a b c d h ↦ hg _ _ _ _ (he a b c d h))).correlation := by
  simp only [correlation, entropy_eq_finiteEntropy_flat, flat_map, finitePush_comp]
  rfl

end StationaryAdditiveLaw
end
end Erdos539Geometry
