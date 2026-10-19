#!/usr/bin/env python3
"""Candidate finite mask certificates. Every generated inequality is kernel checked."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
r=json.loads((ROOT/'data/fresh-geometric-mean-fiber-energy-results.json').read_text())['dimension_weighted_cut_certificate']
header='/-\nCopyright 2026 Sarim Sarfraz\nSPDX-License-Identifier: Apache-2.0\n-/\n'
digits=[]
for line in r['ordered_lines']:
 bits=[1<<i for i in line]
 digits+=bits+[bits[0]+bits[1],bits[2]+bits[3],sum(bits)]
values=['0']+r['v_1_through_13']
s=header+'import Erdos539.PG13Incidence\n\nnamespace Erdos539Geometry\n\n'
s+='def pg13DigitMasks : List ℕ :=\n  ['+', '.join(map(str,digits))+']\n\n'
s+='''def pg13LineDigitMasks (line : List (Fin 13)) : List ℕ :=
  let a := 2 ^ line[0]!.val
  let b := 2 ^ line[1]!.val
  let c := 2 ^ line[2]!.val
  let d := 2 ^ line[3]!.val
  [a, b, c, d, a + b, c + d, a + b + c + d]

theorem pg13DigitMasks_from_lines :
    pg13DigitMasks = pg13LineTable.flatMap pg13LineDigitMasks := by decide +kernel

def pg13MaskCard (m : ℕ) : ℕ := (List.range 13).countP (fun i ↦ m.testBit i)
def pg13MaskWeight (m : ℕ) : ℕ := pg13DigitMasks.countP (fun s ↦ m &&& s != 0)
def pg13MaskComplement (m : ℕ) : ℕ := 8191 ^^^ m

'''
s+='def pg13ExponentTable : List ℚ :=\n  ['+', '.join(v.replace('/',' / ') for v in values)+']\n\n'
s+='''theorem pg13ExponentTable_eq (d : Fin 14) :
    pg13ExponentTable[d.val]! = stationaryCutExponent d.val := by
  fin_cases d <;> norm_num [pg13ExponentTable, stationaryCutExponent_zero,
    stationaryCutExponent_one, '''+', '.join(f'stationaryCutExponent_{k}' for k in range(2,14))+''']

def pg13CutGap (m : ℕ) : ℚ :=
  let p := pg13MaskCard m
  let a := pg13ExponentTable[p]!
  let b := pg13ExponentTable[13 - p]!
  (a * pg13MaskWeight (pg13MaskComplement m) + b * pg13MaskWeight m) / 13 - 4 * (a + b)

def PG13MaskCertificate (m : ℕ) : Prop :=
  pg13MaskCard m ≤ 13 ∧
  pg13MaskCard (pg13MaskComplement m) = 13 - pg13MaskCard m ∧
  56 ≤ max (pg13MaskWeight m) (pg13MaskWeight (pg13MaskComplement m)) ∧
  (0 < m → m < 8191 → (5400 / 4226183 : ℚ) ≤ pg13CutGap m)

instance pg13MaskCertificate_decidable (m : ℕ) : Decidable (PG13MaskCertificate m) := by
  unfold PG13MaskCertificate
  infer_instance

end Erdos539Geometry
'''
(ROOT/'Erdos539/PG13Masks.lean').write_text(s)
for batch in range(64):
 prev='PG13Masks' if batch==0 else f'PG13Mask{batch-1:02d}'
 s=header+f'''import Erdos539.{prev}

namespace Erdos539Geometry

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem pg13_mask_batch_{batch:02d} :
    ∀ i : Fin 128, PG13MaskCertificate ({batch*128} + i.val) := by
  decide +kernel

end Erdos539Geometry
'''
 (ROOT/f'Erdos539/PG13Mask{batch:02d}.lean').write_text(s)
