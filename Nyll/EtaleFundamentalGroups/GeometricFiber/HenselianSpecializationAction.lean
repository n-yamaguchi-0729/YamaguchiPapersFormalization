/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecialization

/-!
# Equivariance of the actual specialization fiber isomorphism

This is the pointwise square for the constructed natural isomorphism, using
actual spectrum precomposition on both geometric points.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H R L : Type u) [CommRing H] [CommRing R]
  [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]
  [IsSepClosed L] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- The actual natural isomorphism intertwines the compatible original
fraction-field and residue-field point actions. -/
theorem henselianSpecializationFiberIso_equivariant
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (X : FiniteEtale (Spec (.of H))) (x : (fiber (Spec.algebraMap H L)).obj X) :
    fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
      ((henselianSpecializationFiberIso H R L).hom.app X
        ((fiberObjEquivHom (Spec.algebraMap H L) X).symm
          (mapPointHom H L σ X (fiberObjEquivHom (Spec.algebraMap H L) X x)))) =
      mapPointHom H (IsLocalRing.ResidueField R) (SchemeTheory.residueAlgEquiv H R τ) X
        (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
          ((henselianSpecializationFiberIso H R L).hom.app X x)) := by
  change fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
      (henselianSpecializationFiberEquiv H R L X
        ((fiberObjEquivHom (Spec.algebraMap H L) X).symm
          (mapPointHom H L σ X (fiberObjEquivHom (Spec.algebraMap H L) X x)))) =
    mapPointHom H (IsLocalRing.ResidueField R) (SchemeTheory.residueAlgEquiv H R τ) X
      (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
        (henselianSpecializationFiberEquiv H R L X x))
  rw [fiberObjEquivHom_henselianSpecializationFiberEquiv, Equiv.apply_symm_apply,
    fiberObjEquivHom_henselianSpecializationFiberEquiv]
  exact henselianSpecializationOverEquiv_equivariant H R L τ σ hσ X _

end AlgebraicGeometry.FiniteEtale
