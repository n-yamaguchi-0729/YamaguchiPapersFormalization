/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Nyll.EtaleFundamentalGroups.Purity.ResidueFieldHullSocle
import Nyll.EtaleFundamentalGroups.Purity.InjectiveResidueFieldCogenerator
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.LeftExact
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finite-length duals into an injective residue-field hull

Restriction of maps into an injective module is surjective.  Together
with left exactness of `Hom`, this gives a short exact sequence dual to
a submodule-quotient sequence.  The dual of a simple module is identified
with the residue field using the socle of its injective hull.  Induction
along a composition series then shows that duality preserves length.
The evaluation map is injective because maps into the hull separate
elements.  Equality of finite lengths makes it an isomorphism.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E]

/-- Every map from a submodule into an injective module extends to the
ambient module, so the linear restriction map is surjective. -/
theorem injective_dualRestriction_surjective [Module.Injective R E]
    {M : Type v} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    Function.Surjective (LinearMap.lcomp R E N.subtype) := by
  intro g
  obtain ⟨f, hf⟩ := Module.Injective.extension_property
    R E N M N.subtype N.subtype_injective g
  exact ⟨f, hf⟩

variable [IsLocalRing R]

private theorem length_linearMap_to_residueFieldHull_of_simple
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] [IsSimpleModule R M] :
    Module.length R (M →ₗ[R] E) = Module.length R M := by
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := R) (M := M)).mp inferInstance
  obtain rfl := IsLocalRing.eq_maximalIdeal hJ
  let : IsSimpleModule R (R ⧸ IsLocalRing.maximalIdeal R) :=
    IsSimpleModule.congr e.symm
  calc
    Module.length R (M →ₗ[R] E) =
        Module.length R ((R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E) :=
      (LinearEquiv.congrLeft E R e).length_eq
    _ = Module.length R (R ⧸ IsLocalRing.maximalIdeal R) :=
      (residueFieldHullHomEquiv i hi hess).length_eq
    _ = 1 := Module.length_eq_one R (R ⧸ IsLocalRing.maximalIdeal R)
    _ = Module.length R M := (Module.length_eq_one R M).symm

/-- Duality into an injective hull of the residue field preserves the
length of each finite-length module. -/
theorem length_linearMap_to_residueFieldHull_of_finiteLength
    [Module.Injective R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (M →ₗ[R] E) = Module.length R M := by
  induction hM with
  | of_subsingleton =>
      rw [Module.length_eq_zero, Module.length_eq_zero]
  | @of_simple_quotient M _ _ N _ hN ih =>
      have hdual : Module.length R (M →ₗ[R] E) =
          Module.length R ((M ⧸ N) →ₗ[R] E) + Module.length R (N →ₗ[R] E) :=
        Module.length_eq_add_of_exact
          (LinearMap.lcomp R E N.mkQ) (LinearMap.lcomp R E N.subtype)
          (LinearMap.lcomp_injective_of_surjective N.mkQ N.mkQ_surjective)
          (injective_dualRestriction_surjective N)
          (LinearMap.exact_lcomp_of_exact_of_surjective E
            (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective)
      have horiginal : Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
        Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
          N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      calc
        Module.length R (M →ₗ[R] E) =
            Module.length R ((M ⧸ N) →ₗ[R] E) + Module.length R (N →ₗ[R] E) := hdual
        _ = Module.length R (M ⧸ N) + Module.length R N := by
          rw [length_linearMap_to_residueFieldHull_of_simple i hi hess, ih]
        _ = Module.length R M := by
          rw [add_comm]
          exact horiginal.symm

/-- The dual of a finite-length module into an injective residue-field
hull again has finite length. -/
theorem isFiniteLength_linearMap_to_residueFieldHull
    [Module.Injective R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    IsFiniteLength R (M →ₗ[R] E) := by
  apply Module.length_ne_top_iff.mp
  rw [length_linearMap_to_residueFieldHull_of_finiteLength i hi hess hM]
  exact Module.length_ne_top_iff.mpr hM

/-- Evaluation into the double dual is bijective on finite-length
modules.  Injectivity separates elements using the residue field;
surjectivity follows because a proper submodule has strictly smaller
length. -/
theorem bijective_residueFieldHullEvaluation_of_finiteLength
    [Module.Injective R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Function.Bijective (residueFieldHullEvaluation R E M) := by
  have hinj : Function.Injective (residueFieldHullEvaluation R E M) :=
    injective_eval_to_injective_residueField i hi M
  refine ⟨hinj, ?_⟩
  have hdual : IsFiniteLength R (M →ₗ[R] E) :=
    isFiniteLength_linearMap_to_residueFieldHull i hi hess hM
  have hdouble : IsFiniteLength R ((M →ₗ[R] E) →ₗ[R] E) :=
    isFiniteLength_linearMap_to_residueFieldHull i hi hess hdual
  let : IsNoetherian R ((M →ₗ[R] E) →ₗ[R] E) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hdouble).1
  let : IsArtinian R ((M →ₗ[R] E) →ₗ[R] E) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hdouble).2
  apply LinearMap.range_eq_top.mp
  by_contra hproper
  have hlt : Module.length R (LinearMap.range (residueFieldHullEvaluation R E M)) <
      Module.length R ((M →ₗ[R] E) →ₗ[R] E) :=
    Submodule.length_lt hproper
  have hrange : Module.length R M =
      Module.length R (LinearMap.range (residueFieldHullEvaluation R E M)) :=
    (LinearEquiv.ofInjective (residueFieldHullEvaluation R E M) hinj).length_eq
  have hlength : Module.length R ((M →ₗ[R] E) →ₗ[R] E) = Module.length R M :=
    (length_linearMap_to_residueFieldHull_of_finiteLength i hi hess hdual).trans
      (length_linearMap_to_residueFieldHull_of_finiteLength i hi hess hM)
  rw [← hrange, hlength] at hlt
  exact (lt_irrefl (Module.length R M)) hlt

/-- The canonical evaluation isomorphism for finite-length modules. -/
noncomputable def residueFieldHullBidualEquiv
    [Module.Injective R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective (residueFieldHullEvaluation R E M)
    (bijective_residueFieldHullEvaluation_of_finiteLength i hi hess hM)

theorem residueFieldHullBidualEquiv_apply
    [Module.Injective R E]
    (i : (R ⧸ IsLocalRing.maximalIdeal R) →ₗ[R] E)
    (hi : Function.Injective i) (hess : IsEssentialSubmodule (LinearMap.range i))
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) (x : M) (f : M →ₗ[R] E) :
    residueFieldHullBidualEquiv i hi hess hM x f = f x := rfl

end EtaleFundamentalGroups.Purity
