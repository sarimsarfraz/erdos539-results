#!/usr/bin/env python3
"""Emit candidate Lean finite-plane definitions; Lean checks every claim.
No generated certificate is trusted without the canonical Lean audit.
"""
from pathlib import Path
from fractions import Fraction
import json
ROOT = Path(__file__).resolve().parents[1]
receipt = json.loads((ROOT / 'data/fresh-geometric-mean-fiber-energy-results.json').read_text())['dimension_weighted_cut_certificate']
header = '/-\nCopyright 2026 Sarim Sarfraz\nSPDX-License-Identifier: Apache-2.0\n-/\n'
lines = receipt['ordered_lines']
points = receipt['projective_points']
s = header + '''import Erdos539.SharpExponents

namespace Erdos539Geometry

/-- The scalar-base-2/3 split recursion in the stationary cut note. -/
def stationaryCutExponent : ℕ → ℚ
  | 0 => 0
  | 1 => 2 / 3
  | n + 2 => (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (n + 1 - i.val)))
termination_by d => d

@[simp] theorem stationaryCutExponent_zero : stationaryCutExponent 0 = 0 := stationaryCutExponent.eq_1
@[simp] theorem stationaryCutExponent_one : stationaryCutExponent 1 = 2 / 3 := stationaryCutExponent.eq_2

theorem stationaryCutExponent_rec (n : ℕ) :
    stationaryCutExponent (n + 2) = (Finset.univ : Finset (Fin (n + 1))).inf' Finset.univ_nonempty
      (fun i ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (n + 1 - i.val))) := stationaryCutExponent.eq_3 n

end Erdos539Geometry
'''
(ROOT/'Erdos539/StationaryCutExponents.lean').write_text(s)
s = header + 'import Erdos539.StationaryCutExponents\nimport Mathlib.Tactic.FinCases\n\nnamespace Erdos539Geometry\n\n'
v = [Fraction(0),Fraction(2,3)]
for d in range(2,14):
 candidates = [(v[p]+v[d-p])/(1+v[p]+v[d-p]) for p in range(1,d)]
 best = min(candidates); p=candidates.index(best)+1; v.append(best)
 assert str(best)==receipt['v_1_through_13'][d-1]
 names = ', '.join(['combineExponent','stationaryCutExponent_one']+[f'stationaryCutExponent_{k}' for k in range(2,d)])
 s += f'''theorem stationaryCutExponent_{d} : stationaryCutExponent {d} = ({best.numerator} / {best.denominator} : ℚ) := by
  rw [show {d} = {d-2} + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin {d-1} ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent ({d-1} - i.val)))
      (Finset.mem_univ (⟨{p-1}, by decide⟩ : Fin {d-1}))
    apply le_trans h
    norm_num [{names}]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i {";" if d == 2 else "<;>"} norm_num [{names}]

'''
s += 'end Erdos539Geometry\n'
(ROOT/'Erdos539/StationaryCutExponentValues.lean').write_text(s)
s = header + '''import Erdos539.StationaryCutExponentValues

namespace Erdos539Geometry

'''
s += 'def pg13PointTable : List (ℕ × ℕ × ℕ) :=\n  ['+', '.join('('+', '.join(map(str,p))+')' for p in points)+']\n\n'
s += 'def pg13LineTable : List (List (Fin 13)) :=\n  [\n'+',\n'.join('    ['+', '.join(map(str,l))+']' for l in lines)+'\n  ]\n\n'
s += '''def pg13Point (i : Fin 13) : ℕ × ℕ × ℕ := pg13PointTable[i.val]!
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
'''
(ROOT/'Erdos539/PG13Incidence.lean').write_text(s)
