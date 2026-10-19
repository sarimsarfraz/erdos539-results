/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntegerCountingCertificate

namespace Erdos539Geometry
open scoped BigOperators

/-- Boolean list operations avoid repeatedly constructing decision proofs
while checking finite counts. The following lemmas link them to the sets. -/
def integerListReflectionCount (L : List ℤ) (w : ℤ) : ℕ :=
  L.countP (fun a ↦ L.contains (w - a))

def integerListEnergy (L : List ℤ) (B : ℕ) : ℕ :=
  ((List.range B).map (fun w : ℕ ↦ integerListReflectionCount L (w : ℤ) ^ 2)).sum

theorem integerListReflectionCount_eq {L : List ℤ} (hL : L.Nodup) (w : ℤ) :
    integerListReflectionCount L w = (integerReflection L.toFinset w).card := by
  rw [integerListReflectionCount, List.countP_eq_length_filter]
  have he : (L.filter (fun a ↦ L.contains (w - a))).toFinset = integerReflection L.toFinset w := by
    ext a
    simp [integerReflection]
  rw [← he, List.toFinset_card_of_nodup (hL.filter _)]

theorem integerListEnergy_eq {L : List ℤ} (hL : L.Nodup) (B : ℕ) :
    integerListEnergy L B = integerIntervalEnergy L.toFinset B := by
  unfold integerListEnergy integerIntervalEnergy
  simp_rw [integerListReflectionCount_eq hL]
  simpa only [List.toFinset_range] using (List.sum_toFinset (fun w : ℕ ↦ (integerReflection L.toFinset w).card ^ 2)
    (List.nodup_range (n := B))).symm

end Erdos539Geometry
