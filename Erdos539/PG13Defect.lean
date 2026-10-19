/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13UnionLaw
import Erdos539.StationaryMixtureEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem pg13UnionEndpoint_additive (T : ℕ) (l : Fin 13)
    (a b c d : fourLeafBranch T) (h : a.val + b.val = c.val + d.val) :
    (pg13UnionEndpoint T (l, a)).val + (pg13UnionEndpoint T (l, b)).val =
      (pg13UnionEndpoint T (l, c)).val + (pg13UnionEndpoint T (l, d)).val := by
  have hp := congrArg (coordinatePadHom (R := ℤ) (pg13LineEmbedding l)) h
  simp only [map_add] at hp
  change coordinatePad (pg13LineEmbedding l) a.val + coordinatePad (pg13LineEmbedding l) b.val =
    coordinatePad (pg13LineEmbedding l) c.val + coordinatePad (pg13LineEmbedding l) d.val at hp
  change (coordinatePad (pg13LineEmbedding l) a.val + pg13BranchOffset T l) +
      (coordinatePad (pg13LineEmbedding l) b.val + pg13BranchOffset T l) =
    (coordinatePad (pg13LineEmbedding l) c.val + pg13BranchOffset T l) +
      (coordinatePad (pg13LineEmbedding l) d.val + pg13BranchOffset T l)
  calc
    _ = (coordinatePad (pg13LineEmbedding l) a.val + coordinatePad (pg13LineEmbedding l) b.val) +
      (pg13BranchOffset T l + pg13BranchOffset T l) := by abel
    _ = (coordinatePad (pg13LineEmbedding l) c.val + coordinatePad (pg13LineEmbedding l) d.val) +
      (pg13BranchOffset T l + pg13BranchOffset T l) := by rw [hp]
    _ = _ := by abel

/-- The actual uniform union law has bounded stationary defect, witnessed
by choosing one line and a stationary quadruple in that branch. -/
theorem pg13Union_defect {T : ℕ} (hT : 0 < T) :
    stationaryEntropyDefect (pg13Union T) (uniformReference (pg13Union T)) ≤
      2 * Real.log 13 + 7 * Real.log 2 := by
  have hP := fourLeafBranch_nonempty hT
  have h := stationaryEntropyDefect_mixture_le (finiteUniformWeight (Fin 13))
    (uniformReference (fourLeafBranch T)) (finiteUniformWeight_nonneg _)
    (finiteUniformWeight_sum _) (fun x ↦ (uniformReference_pos hP x).le)
    (uniformReference_sum hP) (fun l a ↦ pg13UnionEndpoint T (l, a))
    (pg13UnionEndpoint_additive T) (pg13UnionEndpoint_bijective hT).1
  change stationaryEntropyDefect (pg13Union T)
    (finitePush (fun z : Fin 13 × fourLeafBranch T ↦
      finiteUniformWeight (Fin 13) z.1 * uniformReference (fourLeafBranch T) z.2) (pg13UnionEndpoint T)) ≤
        2 * finiteEntropy (finiteUniformWeight (Fin 13)) +
          stationaryEntropyDefect (fourLeafBranch T) (uniformReference (fourLeafBranch T)) at h
  rw [pg13Union_uniform_law hT, finiteUniformWeight_entropy] at h
  norm_num only [Fintype.card_fin, Nat.cast_ofNat] at h
  exact h.trans (add_le_add le_rfl (fourLeafBranch_defect hT))

end
end Erdos539Geometry
