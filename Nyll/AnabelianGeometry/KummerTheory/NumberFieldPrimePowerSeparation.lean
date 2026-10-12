/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PrimePowerSeparation
import Nyll.AnabelianGeometry.KummerTheory.NumberFieldPowerSeparation

/-!
# Prime-power separation over number fields

It suffices to compare cyclic subgroups modulo prime powers. The proof
uses one saturated finitely generated S-unit group for both generators.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace AnabelianGeometry.KummerTheory

variable {K : Type*} [Field K] [NumberField K]

/-- Cyclic subgroup membership is detected by all power quotients of the
multiplicative group of the original number field. -/
theorem numberField_mem_zpowers_of_forall_mem_sup_prime_powers (a b : Kˣ)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ, a ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := Kˣ) (p ^ r)).range) : a ∈ Subgroup.zpowers b := by
  classical
  obtain ⟨A, haA⟩ := exists_sUnitGroup_mem a
  obtain ⟨B, hbB⟩ := exists_sUnitGroup_mem b
  let T := A ∪ B
  let S : Subgroup Kˣ := SUnitGroup (K := K) T
  have hfg : Group.FG S := GroupFG.iff_add_fg.mpr
    (Module.Finite.iff_addGroup_fg.mp (SUnitGroup.moduleFinite (K := K) T))
  have ha : a ∈ S := by
    intro v hv
    exact haA v (fun hvA => hv (Finset.mem_union_left B hvA))
  have hb : b ∈ S := by
    intro v hv
    exact hbB v (fun hvB => hv (Finset.mem_union_right A hvB))
  exact mem_of_forall_mem_sup_prime_powers_of_saturated S (Subgroup.zpowers b)
    (Subgroup.zpowers_le.mpr hb) (mem_sUnitGroup_of_pow_mem T) a ha h

/-- Prime-power quotients determine actual cyclic subgroups, including
their torsion. -/
theorem numberField_zpowers_eq_of_forall_sup_prime_powers_eq (a b : Kˣ)
    (h : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      Subgroup.zpowers a ⊔ (powMonoidHom (α := Kˣ) (p ^ r)).range =
      Subgroup.zpowers b ⊔ (powMonoidHom (α := Kˣ) (p ^ r)).range) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  apply le_antisymm
  · apply Subgroup.zpowers_le.mpr
    apply numberField_mem_zpowers_of_forall_mem_sup_prime_powers
    intro p hp r
    rw [← h p hp r]
    exact (le_sup_left : Subgroup.zpowers a ≤
      Subgroup.zpowers a ⊔ (powMonoidHom (α := Kˣ) (p ^ r)).range)
      (Subgroup.mem_zpowers a)
  · apply Subgroup.zpowers_le.mpr
    apply numberField_mem_zpowers_of_forall_mem_sup_prime_powers
    intro p hp r
    rw [h p hp r]
    exact (le_sup_left : Subgroup.zpowers b ≤
      Subgroup.zpowers b ⊔ (powMonoidHom (α := Kˣ) (p ^ r)).range)
      (Subgroup.mem_zpowers b)

end AnabelianGeometry.KummerTheory
