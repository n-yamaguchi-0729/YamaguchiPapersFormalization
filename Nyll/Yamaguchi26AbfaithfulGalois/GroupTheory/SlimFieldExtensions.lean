/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SlimnessAndTorsion
import Nyll.GaloisCohomology.Topology.FiniteExtensionGalois

/-!
# Slimness and centers under finite field extension

Slimness is preserved by continuous group isomorphisms. A finite extension
of a field with slim absolute Galois group has center-free absolute Galois
group.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- Slimness is preserved by a continuous group isomorphism. -/
theorem isSlim_of_continuousMulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (hG : IsSlim G) : IsSlim H := by
  intro U
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  let V : OpenSubgroup G := U.comap e.toMonoidHom e.continuous
  have hcent : e.symm z ∈ Subgroup.centralizer (V : Set G) := by
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hz (e y) hy
  have hone : e.symm z = 1 := Subgroup.mem_bot.mp ((hG V) ▸ hcent)
  exact e.symm.injective (hone.trans e.symm.map_one.symm)

/-- Slimness of the lower absolute Galois group makes the upper absolute
Galois group center-free for every finite extension. -/
theorem center_eq_bot_absoluteGaloisGroup_of_finiteExtension_of_isSlim
    {K : Type u} {E : Type v} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E]
    (hK : IsSlim Gal(AlgebraicClosure K/K)) :
    Subgroup.center Gal(AlgebraicClosure E/E) = ⊥ := by
  let U := GaloisCohomology.finiteExtensionGaloisOpenSubgroup K E (AlgebraicClosure E)
  have hΩ : IsSlim Gal(AlgebraicClosure E/K) :=
    isSlim_of_continuousMulEquiv
      (KummerTheory.absoluteGaloisClosureEquiv K (AlgebraicClosure E)).symm hK
  let e := GaloisCohomology.finiteExtensionGaloisOpenSubgroupEquiv K E
    (AlgebraicClosure E)
  have hU := openSubgroup_center_eq_bot_of_isSlim hΩ U
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  have hez : e z ∈ Subgroup.center (U : Subgroup Gal(AlgebraicClosure E/K)) := by
    rw [← Subgroup.map_center_eq e.toMulEquiv]
    exact ⟨z, hz, rfl⟩
  have hone : e z = 1 := Subgroup.mem_bot.mp (hU ▸ hez)
  exact e.injective (hone.trans e.map_one.symm)

end Yamaguchi26AbfaithfulGalois
