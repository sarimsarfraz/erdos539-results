/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignedFans

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

theorem maxSignedRestrictedFan_mono (b : Bool) {F G : Finset (ι → ℝ)} (h : F ⊆ G) (I : Finset ι) :
    maxSignedRestrictedFan b F I ≤ maxSignedRestrictedFan b G I := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.card_le_card (signedRestrictedFan_mono b h I a)).trans
    (card_signedRestrictedFan_le_max b I (h ha))

theorem maxTwoRestrictedFan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) (I : Finset ι) :
    maxTwoRestrictedFan F I ≤ maxTwoRestrictedFan G I :=
  max_le_max (maxSignedRestrictedFan_mono true h I) (maxSignedRestrictedFan_mono false h I)

theorem maxTwoFan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) : maxTwoFan F ≤ maxTwoFan G :=
  maxTwoRestrictedFan_mono h ∅

theorem card_signedFan_le_maxTwoFan (b : Bool) {F : Finset (ι → ℝ)} {a : ι → ℝ} (ha : a ∈ F) :
    (signedFan b F a).card ≤ maxTwoFan F := by
  have h := (card_signedRestrictedFan_le_max b ∅ ha).trans (maxSignedRestrictedFan_le_two b F ∅)
  rwa [signedRestrictedFan_empty] at h

end
end Erdos539Geometry
