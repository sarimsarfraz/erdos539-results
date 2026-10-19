/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Incidence

namespace Erdos539Geometry

def pg13LineCoord (l : Fin 13) (i : Fin 4) : Fin 13 := (pg13Line l)[i.val]!

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem pg13_line_coordinates_certificate :
    (∀ l : Fin 13, Function.Injective (pg13LineCoord l)) ∧
    (∀ l j : Fin 13, j ∈ pg13LineSet l ↔ ∃ i : Fin 4, pg13LineCoord l i = j) ∧
    (∀ l : Fin 13, (pg13LineSet l).card = 4) ∧
    (∀ l m : Fin 13, pg13LineSet l = pg13LineSet m → l = m) := by
  decide +kernel

def pg13LineEmbedding (l : Fin 13) : Fin 4 ↪ Fin 13 :=
  ⟨pg13LineCoord l, pg13_line_coordinates_certificate.1 l⟩

theorem pg13_mem_line_iff (l j : Fin 13) :
    j ∈ pg13LineSet l ↔ ∃ i : Fin 4, pg13LineEmbedding l i = j :=
  pg13_line_coordinates_certificate.2.1 l j

theorem pg13LineEmbedding_mem (l : Fin 13) (i : Fin 4) :
    pg13LineEmbedding l i ∈ pg13LineSet l := (pg13_mem_line_iff _ _).mpr ⟨i, rfl⟩

end Erdos539Geometry
