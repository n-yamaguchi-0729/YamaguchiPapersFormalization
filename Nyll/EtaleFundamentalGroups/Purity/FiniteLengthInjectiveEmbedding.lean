/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Nyll.EtaleFundamentalGroups.Purity.InjectiveHullFiniteLengthDual
import Nyll.EtaleFundamentalGroups.Purity.InjectiveResidueFieldCogenerator
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Embedding finite-length modules into finite products of a residue-field hull

A finite generating family of the dual gives finitely many maps that
separate the original finite-length module.  Their product is an
embedding into a finite product of injective hulls.  An embedding of an
essential submodule extends injectively to the ambient module.  If the
hull is Artinian, the ambient module is Artinian as well.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R E : Type u} [CommRing R] [IsLocalRing R]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- Finitely many maps into an injective residue-field hull jointly
embed each finite-length module. -/
theorem exists_injective_linearMap_pi_of_finiteLength
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    ∃ n : ℕ, ∃ j : M →ₗ[R] (Fin n → E), Function.Injective j := by
  have hdual : IsFiniteLength R (M →ₗ[R] E) :=
    isFiniteLength_linearMap_to_residueFieldHull i hi hess hM
  let : IsNoetherian R (M →ₗ[R] E) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hdual).1
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M →ₗ[R] E)
  let j : M →ₗ[R] (Fin n → E) := LinearMap.pi s
  refine ⟨n, j, ?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨f, hf⟩ :=
    exists_linearMap_apply_ne_zero_of_injective_residueField i hi (x - y) hne
  let ev : (M →ₗ[R] E) →ₗ[R] E := residueFieldHullEvaluation R E M (x - y)
  have hspan : Submodule.span R (Set.range s) ≤ LinearMap.ker ev := by
    apply Submodule.span_le.mpr
    rintro g ⟨k, rfl⟩
    change s k (x - y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hxy k)
  rw [hs] at hspan
  have hzero : f ∈ LinearMap.ker ev := hspan (Submodule.mem_top : f ∈ ⊤)
  exact hf hzero

/-- Extending an embedding of an essential finite-length submodule into
a finite product of Artinian injective hulls proves that the ambient
module is Artinian. -/
theorem isArtinian_of_finiteLength_essential_submodule
    [IsArtinian R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : IsEssentialSubmodule N) (hlen : IsFiniteLength R N) :
    IsArtinian R M := by
  obtain ⟨n, j, hj⟩ := exists_injective_linearMap_pi_of_finiteLength i hi hess hlen
  obtain ⟨f, hf⟩ := Module.Injective.extension_property
    R (Fin n → E) N M N.subtype N.subtype_injective j
  have hdisjoint : Disjoint N (LinearMap.ker f) := by
    apply Submodule.disjoint_def.mpr
    intro x hxN hxf
    have hjx : j ⟨x, hxN⟩ = 0 := by
      rw [← hf]
      exact hxf
    have hxzero : (⟨x, hxN⟩ : N) = 0 := hj (hjx.trans j.map_zero.symm)
    exact congrArg Subtype.val hxzero
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp (hN _ hdisjoint)
  exact isArtinian_of_injective f hinj

end EtaleFundamentalGroups.Purity
