/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryIndependentLaw
import Erdos539.FiniteCouplings

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G]

/-- Literal finite additive laws with all four endpoint marginals fixed. -/
def stationaryAdditiveWeights (S : Finset G) (ν : S → ℝ) :
    Set ((S × S) × (S × S) → ℝ) :=
  {p | (∀ z, 0 ≤ p z) ∧
    (∀ z, z.1.1.val + z.1.2.val ≠ z.2.1.val + z.2.2.val → p z = 0) ∧
    finitePush p (fun z ↦ z.1.1) = ν ∧ finitePush p (fun z ↦ z.1.2) = ν ∧
    finitePush p (fun z ↦ z.2.1) = ν ∧ finitePush p (fun z ↦ z.2.2) = ν}

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

theorem flat_mem (Q : StationaryAdditiveLaw S ν) : Q.flat ∈ stationaryAdditiveWeights S ν :=
  ⟨fun z ↦ Q.nonneg z.1.1 z.1.2 z.2.1 z.2.2,
    fun z ↦ Q.supported z.1.1 z.1.2 z.2.1 z.2.2,
    Q.flat_first, Q.flat_second, Q.flat_third, Q.flat_fourth⟩

def ofFlat {p : (S × S) × (S × S) → ℝ} (hp : p ∈ stationaryAdditiveWeights S ν) :
    StationaryAdditiveLaw S ν where
  mass a b c d := p ((a, b), (c, d))
  nonneg a b c d := hp.1 ((a, b), (c, d))
  supported a b c d := hp.2.1 ((a, b), (c, d))
  first a := by rw [← finitePush_first4, hp.2.2.1]
  second b := by rw [← finitePush_second4, hp.2.2.2.1]
  third c := by rw [← finitePush_third4, hp.2.2.2.2.1]
  fourth d := by rw [← finitePush_fourth4, hp.2.2.2.2.2]

theorem ofFlat_entropy {p : (S × S) × (S × S) → ℝ}
    (hp : p ∈ stationaryAdditiveWeights S ν) : (ofFlat hp).entropy = finiteEntropy p := by
  simp only [ofFlat, entropy, finiteEntropy, Fintype.sum_prod_type]

end StationaryAdditiveLaw

theorem stationaryAdditiveWeights_nonempty (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : (stationaryAdditiveWeights S ν).Nonempty :=
  ⟨(independentStationaryAdditiveLaw S ν hν hs).flat,
    (independentStationaryAdditiveLaw S ν hν hs).flat_mem⟩

theorem stationaryAdditiveWeights_isCompact (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : IsCompact (stationaryAdditiveWeights S ν) := by
  let C : Set ((S × S) × (S × S) → ℝ) :=
    {p | ∀ z, z.1.1.val + z.1.2.val ≠ z.2.1.val + z.2.2.val → p z = 0}
  have hC : IsClosed C := by
    simp only [C, Set.setOf_forall]
    apply isClosed_iInter
    intro z
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_apply z) continuous_const
  have he : stationaryAdditiveWeights S ν =
      Set.Icc (0 : (S × S) × (S × S) → ℝ) 1 ∩ C ∩
      {p | finitePush p (fun z ↦ z.1.1) = ν} ∩
      {p | finitePush p (fun z ↦ z.1.2) = ν} ∩
      {p | finitePush p (fun z ↦ z.2.1) = ν} ∩
      {p | finitePush p (fun z ↦ z.2.2) = ν} := by
    ext p
    constructor
    · rintro ⟨hp, hrel, h₁, h₂, h₃, h₄⟩
      refine ⟨⟨⟨⟨⟨⟨hp, ?_⟩, hrel⟩, h₁⟩, h₂⟩, h₃⟩, h₄⟩
      intro z
      have h := le_finitePush p (fun z ↦ z.1.1) hp z
      rw [h₁] at h
      apply h.trans
      change ν z.1.1 ≤ 1
      rw [← hs]
      exact Finset.single_le_sum (fun x _ ↦ hν x) (Finset.mem_univ z.1.1)
    · rintro ⟨⟨⟨⟨⟨⟨hp, _⟩, hrel⟩, h₁⟩, h₂⟩, h₃⟩, h₄⟩
      exact ⟨hp, hrel, h₁, h₂, h₃, h₄⟩
  rw [he]
  exact ((((isCompact_Icc.inter_right hC).inter_right
    (isClosed_eq (by fun_prop) continuous_const)).inter_right
    (isClosed_eq (by fun_prop) continuous_const)).inter_right
    (isClosed_eq (by fun_prop) continuous_const)).inter_right
    (isClosed_eq (by fun_prop) continuous_const)

/-- The entropy maximum exists for every endpoint probability law,
including laws with zero atoms. -/
theorem exists_stationaryAdditiveEntropyMax (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ Q : StationaryAdditiveLaw S ν, ∀ P : StationaryAdditiveLaw S ν, P.entropy ≤ Q.entropy := by
  obtain ⟨p, hp, hmax⟩ := (stationaryAdditiveWeights_isCompact S ν hν hs).exists_isMaxOn
    (stationaryAdditiveWeights_nonempty S ν hν hs) continuous_finiteEntropy.continuousOn
  refine ⟨StationaryAdditiveLaw.ofFlat hp, fun P ↦ ?_⟩
  rw [StationaryAdditiveLaw.ofFlat_entropy]
  have h := hmax P.flat_mem
  simpa only [StationaryAdditiveLaw.entropy, finiteEntropy, StationaryAdditiveLaw.flat,
    Fintype.sum_prod_type] using h

/-- The manuscript's A(nu): the maximum entropy of actual stationary
additive quadruples with endpoint law nu. -/
def stationaryAdditiveEntropy (S : Finset G) (ν : S → ℝ) : ℝ :=
  sSup (finiteEntropy '' stationaryAdditiveWeights S ν)

theorem stationaryAdditiveEntropy_attained (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    ∃ Q : StationaryAdditiveLaw S ν, Q.entropy = stationaryAdditiveEntropy S ν := by
  obtain ⟨Q, hmax⟩ := exists_stationaryAdditiveEntropyMax S ν hν hs
  refine ⟨Q, ?_⟩
  have hg : IsGreatest (finiteEntropy '' stationaryAdditiveWeights S ν) Q.entropy := by
    refine ⟨⟨Q.flat, Q.flat_mem, ?_⟩, ?_⟩
    · simp only [StationaryAdditiveLaw.entropy, finiteEntropy, StationaryAdditiveLaw.flat,
        Fintype.sum_prod_type]
    · rintro _ ⟨p, hp, rfl⟩
      simpa only [StationaryAdditiveLaw.ofFlat_entropy] using hmax (StationaryAdditiveLaw.ofFlat hp)
  exact hg.csSup_eq.symm

theorem stationaryAdditiveEntropy_eq_of_maximal {S : Finset G} {ν : S → ℝ}
    (Q : StationaryAdditiveLaw S ν)
    (hQ : ∀ P : StationaryAdditiveLaw S ν, P.entropy ≤ Q.entropy) :
    stationaryAdditiveEntropy S ν = Q.entropy := by
  have hg : IsGreatest (finiteEntropy '' stationaryAdditiveWeights S ν) Q.entropy := by
    refine ⟨⟨Q.flat, Q.flat_mem, ?_⟩, ?_⟩
    · simp only [StationaryAdditiveLaw.entropy, finiteEntropy, StationaryAdditiveLaw.flat,
        Fintype.sum_prod_type]
    · rintro _ ⟨p, hp, rfl⟩
      simpa only [StationaryAdditiveLaw.ofFlat_entropy] using hQ (StationaryAdditiveLaw.ofFlat hp)
  exact hg.csSup_eq

theorem StationaryAdditiveLaw.entropy_le_stationaryAdditiveEntropy
    {S : Finset G} {ν : S → ℝ} (Q : StationaryAdditiveLaw S ν)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) : Q.entropy ≤ stationaryAdditiveEntropy S ν := by
  obtain ⟨P, hP⟩ := exists_stationaryAdditiveEntropyMax S ν hν hs
  rw [stationaryAdditiveEntropy_eq_of_maximal P hP]
  exact hP Q

/-- The entropy deficiency e(nu), defined using the attained maximum. -/
def stationaryEntropyDefect (S : Finset G) (ν : S → ℝ) : ℝ :=
  3 * finiteEntropy ν - stationaryAdditiveEntropy S ν

theorem stationaryEntropyDefect_bounds (S : Finset G) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    0 ≤ stationaryEntropyDefect S ν ∧ stationaryEntropyDefect S ν ≤ finiteEntropy ν := by
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have hnonneg := Q.correlation_nonneg hν hs
  have hlower := (independentStationaryAdditiveLaw S ν hν hs).entropy_le_stationaryAdditiveEntropy hν hs
  rw [independentStationaryAdditiveLaw_entropy] at hlower
  unfold stationaryEntropyDefect
  unfold StationaryAdditiveLaw.correlation at hnonneg
  rw [hQ] at hnonneg
  constructor <;> linarith

end
end Erdos539Geometry
