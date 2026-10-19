/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13LineCoordinates
import Erdos539.PG13Masks
import Erdos539.FourLeafEncoding

namespace Erdos539Geometry

def pg13DigitSupport (l : Fin 13) (d : Fin 7) : Finset (Fin 13) :=
  Finset.univ.filter (fun j ↦ ∃ i : Fin 4, pg13LineEmbedding l i = j ∧
    d ∈ ({0, fourLeafSibling i, fourLeafLeaf i} : Finset (Fin 7)))

def pg13SupportMask (l : Fin 13) (d : Fin 7) : ℕ :=
  (pg13LineDigitMasks (pg13Line l))[if d = 0 then 6 else if d = 1 then 4
    else if d = 2 then 5 else d.val - 3]!

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem pg13_digit_support_certificate :
    (∀ (l : Fin 13) (d : Fin 7) (j : Fin 13),
      (pg13SupportMask l d).testBit j.val = decide (j ∈ pg13DigitSupport l d)) ∧
    pg13DigitMasks.Perm ((List.ofFn (fun l : Fin 13 ↦ List.ofFn (pg13SupportMask l))).flatten) := by
  decide +kernel

end Erdos539Geometry
