/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13Incidence

namespace Erdos539Geometry

def pg13DigitMasks : List ℕ :=
  [2, 16, 128, 1024, 18, 1152, 1170, 1, 16, 32, 64, 17, 96, 113, 8, 16, 512, 2048, 24, 2560, 2584, 4, 16, 256, 4096, 20, 4352, 4372, 1, 2, 4, 8, 3, 12, 15, 2, 64, 512, 4096, 66, 4608, 4674, 2, 32, 256, 2048, 34, 2304, 2338, 1, 1024, 2048, 4096, 1025, 6144, 7169, 8, 64, 256, 1024, 72, 1280, 1352, 4, 32, 512, 1024, 36, 1536, 1572, 1, 128, 256, 512, 129, 768, 897, 4, 64, 128, 2048, 68, 2176, 2244, 8, 32, 128, 4096, 40, 4224, 4264]

def pg13LineDigitMasks (line : List (Fin 13)) : List ℕ :=
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

def pg13ExponentTable : List ℚ :=
  [0, 2 / 3, 4 / 7, 26 / 47, 8 / 15, 370 / 699, 116 / 221, 766 / 1471, 16 / 31, 1238 / 2403, 3508 / 6823, 23258 / 45323, 488 / 953, 22654 / 44323]

theorem pg13ExponentTable_eq (d : Fin 14) :
    pg13ExponentTable[d.val]! = stationaryCutExponent d.val := by
  fin_cases d <;> norm_num [pg13ExponentTable, stationaryCutExponent_zero,
    stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10, stationaryCutExponent_11, stationaryCutExponent_12, stationaryCutExponent_13]

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
