/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.PowerSeparation
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Rank
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Cyclic power separation over number fields

Although the entire multiplicative group of a number field is not finitely
generated, two prescribed elements lie in one finitely generated S-unit
group. This subgroup is saturated under roots in the original field.
Consequently cyclic subgroups are determined by their images modulo all
positive powers in the original number field.

The power relations here are over the original field. Descending relations
obtained only after adjoining roots of unity is a separate arithmetic step.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace AnabelianGeometry.KummerTheory

variable {K : Type*} [Field K] [NumberField K]

/-- Every nonzero element has finite support at the finite places. -/
theorem exists_sUnitGroup_mem (a : Kˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), a ∈ SUnitGroup (K := K) S := by
  obtain ⟨S, hS⟩ := IdeleGroup.exists_finset_supportedAt (IdeleGroup.principalIdele K a)
  refine ⟨S, ?_⟩
  rw [mem_SUnitGroup_iff]
  intro v hv
  have hunit := (IdeleGroup.mem_supportedAt_iff (K := K) (S : Set _)
    (IdeleGroup.principalIdele K a)).mp hS v hv
  rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hunit
  change Valued.v (((IdeleGroup.finiteComponent v
    (IdeleGroup.principalIdele K a) : (v.adicCompletion K)ˣ) : v.adicCompletion K)) = 1
    at hunit
  rw [IdeleGroup.finiteComponent_principalIdele,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hunit
  exact hunit

/-- An element of the number field whose positive power is an S-unit is
itself an S-unit. -/
theorem mem_sUnitGroup_of_pow_mem
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) (y : Kˣ)
    (hy : y ^ (n : ℕ) ∈ SUnitGroup (K := K) S) :
    y ∈ SUnitGroup (K := K) S := by
  rw [mem_SUnitGroup_iff] at hy ⊢
  intro v hv
  have hp : (v.valuation K (y : K)) ^ (n : ℕ) = 1 := by
    rw [← map_pow]
    exact hy v hv
  exact (pow_eq_one_iff_left n.ne_zero).mp hp

/-- Cyclic subgroup membership is detected by all power quotients of the
multiplicative group of the original number field. -/
theorem numberField_mem_zpowers_of_forall_mem_sup_powers (a b : Kˣ)
    (h : ∀ n : ℕ+, a ∈ Subgroup.zpowers b ⊔
      (powMonoidHom (α := Kˣ) (n : ℕ)).range) : a ∈ Subgroup.zpowers b := by
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
  exact mem_of_forall_mem_sup_powers_of_saturated S (Subgroup.zpowers b)
    (Subgroup.zpowers_le.mpr hb) (mem_sUnitGroup_of_pow_mem T) a ha h

/-- Over a number field, intersecting all ambient-power enlargements of
a cyclic subgroup recovers precisely that subgroup. -/
theorem numberField_iInf_zpowers_sup_powers (a : Kˣ) :
    (⨅ n : ℕ+, Subgroup.zpowers a ⊔
      (powMonoidHom (α := Kˣ) (n : ℕ)).range) = Subgroup.zpowers a := by
  apply le_antisymm
  · intro b hb
    exact numberField_mem_zpowers_of_forall_mem_sup_powers b a
      (Subgroup.mem_iInf.mp hb)
  · exact le_iInf fun _ => le_sup_left

/-- Matching cyclic subgroups modulo every positive power in a number
field implies equality of the actual cyclic subgroups. -/
theorem numberField_zpowers_eq_of_forall_sup_powers_eq (a b : Kˣ)
    (h : ∀ n : ℕ+,
      Subgroup.zpowers a ⊔ (powMonoidHom (α := Kˣ) (n : ℕ)).range =
      Subgroup.zpowers b ⊔ (powMonoidHom (α := Kˣ) (n : ℕ)).range) :
    Subgroup.zpowers a = Subgroup.zpowers b := by
  rw [← numberField_iInf_zpowers_sup_powers a,
    ← numberField_iInf_zpowers_sup_powers b]
  exact iInf_congr h

end AnabelianGeometry.KummerTheory
