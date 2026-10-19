/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryCutExponentValues

namespace Erdos539Geometry

def pg13PointTable : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 1), (0, 1, 0), (0, 1, 1), (0, 1, 2), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 0), (1, 2, 1), (1, 2, 2)]

def pg13LineTable : List (List (Fin 13)) :=
  [
    [1, 4, 7, 10],
    [0, 4, 5, 6],
    [3, 4, 9, 11],
    [2, 4, 8, 12],
    [0, 1, 2, 3],
    [1, 6, 9, 12],
    [1, 5, 8, 11],
    [0, 10, 11, 12],
    [3, 6, 8, 10],
    [2, 5, 9, 10],
    [0, 7, 8, 9],
    [2, 6, 7, 11],
    [3, 5, 7, 12]
  ]

def pg13Point (i : Fin 13) : ℕ × ℕ × ℕ := pg13PointTable[i.val]!
def pg13Line (i : Fin 13) : List (Fin 13) := pg13LineTable[i.val]!
def pg13LineSet (i : Fin 13) : Finset (Fin 13) := (pg13Line i).toFinset

def pg13Dot (i j : Fin 13) : ℕ :=
  (pg13Point i).1 * (pg13Point j).1 +
  (pg13Point i).2.1 * (pg13Point j).2.1 +
  (pg13Point i).2.2 * (pg13Point j).2.2

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem pg13_incidence_certificate :
    pg13PointTable.length = 13 ∧ pg13PointTable.Nodup ∧
    pg13LineTable.length = 13 ∧
    (∀ i : Fin 13, (pg13Line i).length = 4 ∧ (pg13Line i).Nodup) ∧
    (∀ i j : Fin 13, j ∈ pg13LineSet i ↔ pg13Dot i j % 3 = 0) ∧
    (∀ i : Fin 13, ((Finset.univ : Finset (Fin 13)).filter (fun j ↦ i ∈ pg13LineSet j)).card = 4) ∧
    (∀ i j : Fin 13, i ≠ j → (pg13LineSet i ∩ pg13LineSet j).card = 1) := by
  decide +kernel

end Erdos539Geometry
