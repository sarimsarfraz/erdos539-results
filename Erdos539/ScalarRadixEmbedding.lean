/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectedCountingTransport

namespace Erdos539Geometry
noncomputable section
open scoped Pointwise Classical

def scalarRadixMap (m : ℤ) : ℤ × ℤ →+ ℤ where
  toFun p := p.1 + m * p.2
  map_zero' := by simp
  map_add' := by intro p q; dsimp; ring

theorem scalarRadixMap_injOn {U V : Finset ℤ} {m : ℤ} (hm : 0 < m)
    (hU : ∀ a ∈ U, 0 ≤ a ∧ a < m) :
    Set.InjOn (scalarRadixMap m) (↑(U ×ˢ V) : Set (ℤ × ℤ)) := by
  intro p hp q hq he
  have hp' := hU p.1 (Finset.mem_product.mp hp).1
  have hq' := hU q.1 (Finset.mem_product.mp hq).1
  have he' : p.1 + m * p.2 = q.1 + m * q.2 := he
  have hemod := congrArg (fun x : ℤ ↦ x % m) he'
  simp only [Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt hp'.1 hp'.2, Int.emod_eq_of_lt hq'.1 hq'.2] at hemod
  apply Prod.ext hemod
  rw [hemod] at he'
  exact mul_left_cancel₀ hm.ne' (add_left_cancel he')

theorem scalarRadixMap_injOn_support_and_sums {U V : Finset ℤ} {m : ℤ} (hm : 0 < m)
    (hU : ∀ a ∈ U, 0 ≤ a ∧ 2 * a < m) :
    Set.InjOn (scalarRadixMap m) (↑(U ×ˢ V) : Set (ℤ × ℤ)) ∧
    Set.InjOn (scalarRadixMap m) (↑((U ×ˢ V) + (U ×ˢ V)) : Set (ℤ × ℤ)) := by
  constructor
  · apply scalarRadixMap_injOn hm
    intro a ha
    have h := hU a ha
    constructor <;> omega
  · rw [product_sumset]
    apply scalarRadixMap_injOn hm
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hw
    have ha' := hU a ha
    have hb' := hU b hb
    constructor <;> omega

end
end Erdos539Geometry
