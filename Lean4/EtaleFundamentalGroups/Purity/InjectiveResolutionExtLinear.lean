/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Linear cocycle quotients for Ext from an injective resolution

The cocycle constructor for derived-category Ext is linear. Its surjectivity
and its explicit coboundary criterion identify the quotient of cocycles by
coboundaries with positive-degree Ext over the original scalar ring.
-/

noncomputable section

open CategoryTheory Opposite

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]
variable {M : ModuleCat.{u} R}

/-- The complex of linear morphisms into a chosen injective resolution. -/
def injectiveResolutionLinearCoyonedaComplex
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  ((((linearCoyoneda R (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj J.cocomplex)

/-- The adjacent three terms computing positive-degree Ext. -/
def injectiveResolutionLinearCoyonedaShortComplexSucc
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  (injectiveResolutionLinearCoyonedaComplex J X).sc' n (n + 1) (n + 2)

/-- Scalar compatibility of the injective-resolution cocycle constructor. -/
theorem injectiveResolution_extMk_smul
    (J : InjectiveResolution M) {X : ModuleCat.{u} R} {n : ℕ}
    (f : X ⟶ J.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ J.cocomplex.d n m = 0) (a : R) :
    J.extMk (a • f) m hm (by
      rw [Linear.smul_comp, hf, smul_zero]) =
      a • J.extMk f m hm hf := by
  have h := J.mk₀_comp_extMk f m hm hf (a • 𝟙 X)
  simpa only [Linear.smul_comp, Category.id_comp,
    Abelian.Ext.mk₀_smul, Abelian.Ext.smul_comp,
    Abelian.Ext.mk₀_id_comp] using h.symm

/-- A linear map from the cocycles in the Hom complex to Ext. -/
def injectiveResolutionCyclesToExtSucc
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ) :
    LinearMap.ker
        (injectiveResolutionLinearCoyonedaShortComplexSucc J X n).g.hom →ₗ[R]
      Abelian.Ext.{u} X M (n + 1) where
  toFun f := J.extMk f.1 (n + 2) (by omega) (by
    change f.1 ≫ J.cocomplex.d (n + 1) (n + 2) = 0
    exact f.2)
  map_add' f g := (J.add_extMk f.1 g.1 (n + 2) (by omega) f.2 g.2).symm
  map_smul' a f := injectiveResolution_extMk_smul J f.1 (n + 2) (by omega) f.2 a

theorem injectiveResolutionCyclesToExtSucc_surjective
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ) :
    Function.Surjective (injectiveResolutionCyclesToExtSucc J X n) := by
  intro α
  obtain ⟨f, hf, rfl⟩ := J.extMk_surjective α (n + 2) (by omega)
  exact ⟨⟨f, hf⟩, rfl⟩

/-- The kernel of the cocycle constructor is precisely the coboundaries. -/
theorem injectiveResolutionCyclesToExtSucc_ker_eq_range
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ) :
    LinearMap.ker (injectiveResolutionCyclesToExtSucc J X n) =
      LinearMap.range
        (injectiveResolutionLinearCoyonedaShortComplexSucc J X n).moduleCatToCycles := by
  ext f
  change J.extMk f.1 (n + 2) (by omega) f.2 = 0 ↔ _
  rw [J.extMk_eq_zero_iff f.1 (n + 2) (by omega) f.2 n rfl]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congr_arg Subtype.val hg⟩

/-- Positive Ext is the linear quotient of explicit cocycles by boundaries. -/
def injectiveResolutionCocycleQuotientEquivExtSucc
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ) :
    ((LinearMap.ker
        (injectiveResolutionLinearCoyonedaShortComplexSucc J X n).g.hom) ⧸
      LinearMap.range
        (injectiveResolutionLinearCoyonedaShortComplexSucc J X n).moduleCatToCycles) ≃ₗ[R]
      Abelian.Ext.{u} X M (n + 1) :=
  (Submodule.quotEquivOfEq _ _
      (injectiveResolutionCyclesToExtSucc_ker_eq_range J X n).symm).trans
    ((injectiveResolutionCyclesToExtSucc J X n).quotKerEquivOfSurjective
      (injectiveResolutionCyclesToExtSucc_surjective J X n))

theorem injectiveResolutionCocycleQuotientEquivExtSucc_apply_mk
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ)
    (f : LinearMap.ker
      (injectiveResolutionLinearCoyonedaShortComplexSucc J X n).g.hom) :
    injectiveResolutionCocycleQuotientEquivExtSucc J X n (Submodule.Quotient.mk f) =
      J.extMk f.1 (n + 2) (by omega) f.2 :=
  rfl

theorem injectiveResolutionCocycleQuotientEquivExtSucc_symm_extMk
    (J : InjectiveResolution M) (X : ModuleCat.{u} R) (n : ℕ)
    (f : X ⟶ J.cocomplex.X (n + 1))
    (hf : f ≫ J.cocomplex.d (n + 1) (n + 2) = 0) :
    (injectiveResolutionCocycleQuotientEquivExtSucc J X n).symm
        (J.extMk f (n + 2) (by omega) hf) =
      Submodule.Quotient.mk ⟨f, hf⟩ :=
  (injectiveResolutionCocycleQuotientEquivExtSucc J X n).symm_apply_apply
    (Submodule.Quotient.mk ⟨f, hf⟩)

end EtaleFundamentalGroups.Purity

end
