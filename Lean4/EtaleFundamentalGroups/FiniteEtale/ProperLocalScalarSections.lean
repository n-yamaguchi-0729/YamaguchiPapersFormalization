/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ProperLocalSectionAlgebra
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar sections after arbitrary base change

For a proper flat geometrically reduced family over a Noetherian local ring,
an isomorphism on the actual global-section map persists after arbitrary
base change. This uses the proved section-algebra comparison and the actual
tensor-product scalar inclusion, including nonflat residue-field changes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

open Scheme.TwoAffineOpenCover

/-- Scalar global sections persist after any coefficient change for a proper
flat geometrically reduced family over a Noetherian local ring. -/
theorem isIso_appTop_baseChange_of_proper_flat_geometricallyReduced_local
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [GeometricallyReduced f] [IsIso f.appTop]
    (A : Type u) [CommRing A] [Algebra R A] :
    IsIso (pullback.snd f (specMap R A)).appTop := by
  let hRΓ : Algebra R Γ(X, ⊤) := algebraOfHom f ⊤
  let fA := pullback.snd f (specMap R A)
  let hAΓ : Algebra A Γ(pullback f (specMap R A), ⊤) := algebraOfHom fA ⊤
  obtain ⟨e, _⟩ := (finite_projective_sectionAlgebra_and_baseChange_local f).2 A
  have hScalar : Function.Bijective (algebraMap R Γ(X, ⊤)) := by
    change Function.Bijective
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ ⊤ le_top).hom)
    have hApp : f.appTop = f.appLE ⊤ ⊤ le_top := f.app_eq_appLE
    rw [← hApp]
    exact ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop)
  have hInclude : Function.Bijective
      (Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[R] Γ(X, ⊤)) :=
    Algebra.TensorProduct.includeLeft_bijective hScalar
  have hAfter : Function.Bijective (algebraMap A Γ(pullback f (specMap R A), ⊤)) := by
    have hMap : e ∘ (Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[R] Γ(X, ⊤)) =
        algebraMap A Γ(pullback f (specMap R A), ⊤) := by
      funext a
      exact e.commutes a
    exact hMap ▸ e.bijective.comp hInclude
  have hIso : IsIso ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ fA.appTop) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hApp : fA.appTop = fA.appLE ⊤ ⊤ le_top := fA.app_eq_appLE
    change Function.Bijective (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      fA.appLE ⊤ ⊤ le_top).hom) at hAfter
    rw [← hApp] at hAfter
    exact hAfter
  exact (isIso_comp_left_iff (Scheme.ΓSpecIso (CommRingCat.of A)).inv fA.appTop).mp hIso

end AlgebraicGeometry
