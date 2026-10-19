/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryLawComposition
import Erdos539.StationaryFanCapacity
import Erdos539.FiniteEntropySubadditive
import Erdos539.CoordinateSweep

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance quadrupleFanEncodingDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The two anchored positive outputs retain the two last endpoints. -/
def quadrupleFanEncoding (S : Finset (ι → ℝ)) (t : (S × S) × (S × S)) :
    (S × posDiff S) × (S × posDiff S) :=
  ((t.2.1, positiveDifferenceChannel S t.2.1 t.1.1),
    (t.2.2, positiveDifferenceChannel S t.2.2 t.1.2))

namespace StationaryAdditiveLaw
variable {S : Finset (ι → ℝ)} {ν : S → ℝ}

/-- Direct injectivity on the nonzero additive support. No sign mask,
symmetry assumption, or reflected replacement of the law is used. -/
theorem fan_encoding_injective_on_support (Q : StationaryAdditiveLaw S ν)
    (u v : (S × S) × (S × S)) (hu : Q.flat u ≠ 0) (hv : Q.flat v ≠ 0)
    (he : quadrupleFanEncoding S u = quadrupleFanEncoding S v) : u = v := by
  rcases u with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rcases v with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
  have hc : c = c' := congrArg (fun z ↦ z.1.1) he
  have hd : d = d' := congrArg (fun z ↦ z.2.1) he
  subst c'
  subst d'
  have hz : pdiff a.val c.val = pdiff a'.val c.val := congrArg (fun z ↦ z.1.2.val) he
  have hw : pdiff b.val d.val = pdiff b'.val d.val := congrArg (fun z ↦ z.2.2.val) he
  have hr : a.val + b.val = c.val + d.val := by
    by_contra hn
    exact hu (Q.supported a b c d hn)
  have hr' : a'.val + b'.val = c.val + d.val := by
    by_contra hn
    exact hv (Q.supported a' b' c d hn)
  have hrev {x y : S} (hrel : x.val + y.val = c.val + d.val) :
      pdiff c.val x.val = pdiff y.val d.val := by
    funext i
    have hi := congrFun hrel i
    change max (c.val i - x.val i) 0 = max (y.val i - d.val i) 0
    congr 1
    change x.val i + y.val i = c.val i + d.val i at hi
    linarith
  have ha : a = a' := Subtype.ext ((anchored_split_injective c.val)
    (Prod.ext hz (by
      change pdiff c.val a.val = pdiff c.val a'.val
      rw [hrev hr, hrev hr', hw])))
  subst a'
  have hb : b = b' := Subtype.ext (add_left_cancel (hr.trans hr'.symm))
  subst b'
  rfl

/-- Entropy is preserved by the literal two-fan encoding. -/
theorem fan_encoding_entropy (Q : StationaryAdditiveLaw S ν) :
    finiteEntropy (finitePush Q.flat (quadrupleFanEncoding S)) = Q.entropy := by
  rw [Q.entropy_eq_finiteEntropy_flat]
  exact finiteEntropy_push_eq_of_support_injective Q.flat (quadrupleFanEncoding S)
    Q.fan_encoding_injective_on_support

/-- Every selected pair of endpoint observations with marginal nu
induces a legitimate stationary fan coupling. -/
theorem endpoint_fan_entropy_le (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    (C X : (S × S) × (S × S) → S)
    (hC : finitePush Q.flat C = ν) (hX : finitePush Q.flat X = ν) :
    finiteEntropy (finitePush Q.flat (fun t ↦ (C t, positiveDifferenceChannel S (C t) (X t)))) ≤
      finiteEntropy ν + stationaryFanCapacity S ν := by
  let p := finitePush Q.flat (fun t ↦ (C t, X t))
  have hp : p ∈ stationaryCouplings ν := by
    refine ⟨finitePush_nonneg Q.flat _ (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2), ?_, ?_⟩
    · rw [finitePush_comp]; exact hC
    · rw [finitePush_comp]; exact hX
  have h := couplingOutputEntropy_le_stationaryCapacity ν hν hs (positiveDifferenceChannel S) p hp
  unfold couplingOutputEntropy at h
  rw [finitePush_comp] at h
  change finiteEntropy (finitePush Q.flat (fun t ↦ (C t, positiveDifferenceChannel S (C t) (X t)))) -
    finiteEntropy ν ≤ stationaryFanCapacity S ν at h
  linarith

/-- The dimension-free direct encoding inequality for every actual
stationary additive law, including laws with zero atoms. -/
theorem entropy_le_two_fans (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    Q.entropy ≤ 2 * finiteEntropy ν + 2 * stationaryFanCapacity S ν := by
  let p := finitePush Q.flat (quadrupleFanEncoding S)
  have hp : ∀ t, 0 ≤ p t := finitePush_nonneg Q.flat _
    (fun t ↦ Q.nonneg t.1.1 t.1.2 t.2.1 t.2.2)
  have htotal : ∑ t, Q.flat t = 1 := by
    simp only [flat, Fintype.sum_prod_type]
    exact Q.total_mass hs
  have hsub := finiteEntropy_subadditive p hp (by rw [finitePush_sum, htotal])
  have hleft := Q.endpoint_fan_entropy_le hν hs (fun t ↦ t.2.1) (fun t ↦ t.1.1)
    Q.flat_third Q.flat_first
  have hright := Q.endpoint_fan_entropy_le hν hs (fun t ↦ t.2.2) (fun t ↦ t.1.2)
    Q.flat_fourth Q.flat_second
  have he : finiteEntropy p = Q.entropy := Q.fan_encoding_entropy
  dsimp only [p] at hsub
  rw [finitePush_comp, finitePush_comp] at hsub
  change finiteEntropy p ≤ _ at hsub
  rw [he] at hsub
  change Q.entropy ≤ finiteEntropy (finitePush Q.flat (fun t ↦
    (t.2.1, positiveDifferenceChannel S t.2.1 t.1.1))) +
      finiteEntropy (finitePush Q.flat (fun t ↦ (t.2.2, positiveDifferenceChannel S t.2.2 t.1.2))) at hsub
  linarith

end StationaryAdditiveLaw
end
end Erdos539Geometry
