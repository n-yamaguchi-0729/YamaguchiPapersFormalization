/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.EssentialModuleExtension
import EtaleFundamentalGroups.Purity.EssentialModuleMaps
import EtaleFundamentalGroups.Purity.EssentialModuleMaximalExtension
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Injective envelopes inside an injective ambient module

Choose a maximal essential extension `E` of a submodule `N` inside an
injective module `M`.  Quotienting `M` by a maximal submodule disjoint from
`E` gives an essential extension of `E`.  Injectivity of `M` extends the
inclusion of `E` to a map from this quotient into `M`.  Its image is again
an essential extension of `N`, hence equals `E` by maximality.

The resulting map `M → E` retracts the inclusion.  Extending maps from
ideals into `M` and composing with this retraction proves Baer's criterion
for `E`.
-/

namespace EtaleFundamentalGroups.Purity

universe u

/-- A submodule of an injective module admits an injective essential
extension within that same ambient module. -/
theorem exists_injective_essential_extension
    {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Injective R M] (N : Submodule R M) :
    ∃ E : Submodule R M, N ≤ E ∧
      IsEssentialSubmodule (N.comap E.subtype) ∧ Module.Injective R E := by
  obtain ⟨E, hNE, hNess, hmax⟩ := exists_maximal_essential_extension N
  obtain ⟨P, hEP, hEPess⟩ := exists_disjoint_essential_quotient E
  let i : E →ₗ[R] M ⧸ P := P.mkQ.comp E.subtype
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    change P.mkQ (a : M) = P.mkQ (b : M) at hab
    have hzero : P.mkQ ((a : M) - (b : M)) = 0 := by
      rw [map_sub, hab, sub_self]
    have hmemP : (a : M) - (b : M) ∈ P :=
      (Submodule.Quotient.mk_eq_zero P).mp hzero
    exact sub_eq_zero.mp
      ((Submodule.disjoint_def.mp hEP) ((a : M) - (b : M))
        (E.sub_mem a.property b.property) hmemP)
  obtain ⟨f, hfi⟩ := Module.Injective.extension_property
    R M E (M ⧸ P) i hi E.subtype
  have hfe (e : E) : f (P.mkQ (e : M)) = (e : M) :=
    DFunLike.congr_fun hfi e
  let S : Submodule R M := LinearMap.range f
  have hES : E ≤ S := by
    intro e he
    exact ⟨P.mkQ e, hfe ⟨e, he⟩⟩
  have hEinside :
      ∀ L : Submodule R M, L ≤ S → Disjoint E L → L = ⊥ := by
    intro L hLS hEL
    have hpre : Disjoint (E.map P.mkQ) (L.comap f) := by
      apply Submodule.disjoint_def.mpr
      intro z hzE hzL
      obtain ⟨e, he, hez⟩ := Submodule.mem_map.mp hzE
      have hfz : f z = e := by
        rw [← hez]
        exact hfe ⟨e, he⟩
      have heL : e ∈ L := hfz ▸ (Submodule.mem_comap.mp hzL)
      have heZero : e = 0 := (Submodule.disjoint_def.mp hEL) e he heL
      rw [← hez, heZero, map_zero]
    have hpreZero : L.comap f = ⊥ := hEPess (L.comap f) hpre
    apply le_antisymm ?_ bot_le
    intro z hzL
    obtain ⟨w, hw⟩ := hLS hzL
    have hwL : w ∈ L.comap f := Submodule.mem_comap.mpr (hw.symm ▸ hzL)
    rw [hpreZero] at hwL
    have hwZero : w = 0 := (Submodule.mem_bot R).mp hwL
    have hzZero : z = 0 := hw.symm.trans (by rw [hwZero, map_zero])
    exact (Submodule.mem_bot R).mpr hzZero
  have hNinside :
      ∀ L : Submodule R M, L ≤ E → Disjoint N L → L = ⊥ :=
    (isEssentialSubmodule_comap_subtype_iff N E hNE).mp hNess
  have hNSess : IsEssentialSubmodule (N.comap S.subtype) := by
    apply (isEssentialSubmodule_comap_subtype_iff N S (hNE.trans hES)).mpr
    intro L hLS hNL
    apply hEinside L hLS
    apply disjoint_iff.mpr
    exact hNinside (E ⊓ L) inf_le_left (hNL.mono_right inf_le_right)
  have hSE : S = E := hmax S hES hNSess
  let r : M →ₗ[R] E :=
    LinearMap.codRestrict E (f.comp P.mkQ) (by
      intro m
      rw [← hSE]
      exact ⟨P.mkQ m, rfl⟩)
  have hr (e : E) : r (e : M) = e := by
    apply Subtype.ext
    exact hfe e
  refine ⟨E, hNE, hNess, ?_⟩
  apply Module.Baer.injective
  intro I g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property
    R M I R I.subtype I.injective_subtype (E.subtype.comp g)
  refine ⟨r.comp h, ?_⟩
  intro x hx
  change r (h x) = g ⟨x, hx⟩
  have hhx : h x = (g ⟨x, hx⟩ : M) := DFunLike.congr_fun hh ⟨x, hx⟩
  rw [hhx]
  exact hr (g ⟨x, hx⟩)

end EtaleFundamentalGroups.Purity
