/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageQuadrupleLaw
import Erdos539.SeparatedComponentEnergy
import Erdos539.SidonQuadrupleEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq H]
local instance separatedImageEntropyDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem imageFlat_supported_unordered (Q : StationaryAdditiveLaw S ν) (φ : G → H)
    (hsep : SeparatedSumLabels S φ) {z : ((S.image φ) × (S.image φ)) × ((S.image φ) × (S.image φ))}
    (hp : Q.imageFlat φ z ≠ 0) : SameUnorderedPair z.1.1 z.1.2 z.2.1 z.2.2 := by
  by_contra hbad
  apply hp
  apply finitePush_eq_zero_of_fiber_zero
  intro x hx
  apply Q.supported
  intro hrel
  have he := hsep x.1.1.val x.1.1.property x.1.2.val x.1.2.property
    x.2.1.val x.2.1.property x.2.2.val x.2.2.property hrel
  have ha := congrArg (fun t ↦ t.1.1.val) hx
  have hb := congrArg (fun t ↦ t.1.2.val) hx
  have hc := congrArg (fun t ↦ t.2.1.val) hx
  have hd := congrArg (fun t ↦ t.2.2.val) hx
  change φ x.1.1.val = z.1.1.val at ha
  change φ x.1.2.val = z.1.2.val at hb
  change φ x.2.1.val = z.2.1.val at hc
  change φ x.2.2.val = z.2.2.val at hd
  rw [ha, hb, hc, hd] at he
  apply hbad
  rcases he with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · exact Or.inl ⟨Subtype.ext hac, Subtype.ext hbd⟩
  · exact Or.inr ⟨Subtype.ext had, Subtype.ext hbc⟩

/-- The sharp Sidon entropy coefficient applies to the actual component
labels of every stationary parent law with positive endpoints. -/
theorem separated_image_entropy_le (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 < ν x) (hs : ∑ x, ν x = 1) (φ : G → H) (hsep : SeparatedSumLabels S φ) :
    finiteEntropy (Q.imageFlat φ) ≤ sharpSidonExponent * finiteEntropy (finitePush ν (imageEndpoint S φ)) :=
  sidonQuadruple_entropy_le (Q.imageFlat φ) (finitePush ν (imageEndpoint S φ))
    (Q.imageFlat_nonneg φ) (Q.imageFlat_sum φ hs) (finitePush_imageEndpoint_pos S φ ν hν)
    (by rw [finitePush_sum, hs]) (fun _ hp ↦ Q.imageFlat_supported_unordered φ hsep hp)
    (Q.imageFlat_endpoint_expectation φ)

end StationaryAdditiveLaw
end
end Erdos539Geometry
