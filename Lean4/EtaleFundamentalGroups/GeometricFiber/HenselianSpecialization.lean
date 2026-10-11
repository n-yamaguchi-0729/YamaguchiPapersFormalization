/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.PointSections
import SchemeTheory.FiniteEtale.Algebra.PointSpecialization
import EtaleFundamentalGroups.GeometricFiber.BasePoint
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup

/-!
# The actual specialization comparison of geometric fibers

Finite étale points in the fraction field of a normal henselian local ring
specialize bijectively to residue-field points. The canonical section
correspondence turns this same specialization into a natural isomorphism of
geometric fiber functors. Its pointwise action is compatible with the actual
normal-local-ring and fraction-field automorphisms.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (H R L : Type u) [CommRing H] [CommRing R]
  [HenselianLocalRing R] [IsIntegrallyClosed R] [Field L]
  [Algebra H R] [Algebra R L] [IsFractionRing R L]
  [Algebra H L] [IsScalarTower H R L]

local instance finiteSections (X : FiniteEtale (Spec (.of H))) :
    Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X

/-- Specialization of actual over-points, through their canonical section maps. -/
def henselianSpecializationOverEquiv (X : FiniteEtale (Spec (.of H))) :
    (Over.mk (Spec.algebraMap H L) ⟶ X.toComma) ≃
      (Over.mk (Spec.algebraMap H (IsLocalRing.ResidueField R)) ⟶ X.toComma) :=
  (pointHomAlgEquiv H L X).trans
    ((SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)).trans
      (pointHomAlgEquiv H (IsLocalRing.ResidueField R) X).symm)

/-- The over-point comparison is exactly the previously constructed ring specialization. -/
theorem pointHomAlgEquiv_henselianSpecializationOverEquiv
    (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H L) ⟶ X.toComma) :
    pointHomAlgEquiv H (IsLocalRing.ResidueField R) X
        (henselianSpecializationOverEquiv H R L X x) =
      SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
        (pointHomAlgEquiv H L X x) :=
  Equiv.apply_symm_apply _ _

/-- Specialization is natural for the original finite étale-cover morphisms. -/
theorem henselianSpecializationOverEquiv_naturality
    {X Y : FiniteEtale (Spec (.of H))} (f : X ⟶ Y)
    (x : Over.mk (Spec.algebraMap H L) ⟶ X.toComma) :
    henselianSpecializationOverEquiv H R L Y (x ≫ f.hom) =
      henselianSpecializationOverEquiv H R L X x ≫ f.hom := by
  apply (pointHomAlgEquiv H (IsLocalRing.ResidueField R) Y).injective
  calc
    _ = SchemeTheory.finiteEtalePointSpecialization H R L Γ(Y.left, ⊤)
        (pointHomAlgEquiv H L Y (x ≫ f.hom)) :=
      pointHomAlgEquiv_henselianSpecializationOverEquiv H R L Y _
    _ = SchemeTheory.finiteEtalePointSpecialization H R L Γ(Y.left, ⊤)
        ((pointHomAlgEquiv H L X x).comp (sectionsAlgHom H f)) :=
      congrArg (SchemeTheory.finiteEtalePointSpecialization H R L Γ(Y.left, ⊤))
        (pointHomAlgEquiv_naturality H L f x)
    _ = (SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
        (pointHomAlgEquiv H L X x)).comp (sectionsAlgHom H f) :=
      SchemeTheory.finiteEtalePointSpecialization_naturality H R L Γ(X.left, ⊤)
        (sectionsAlgHom H f) (pointHomAlgEquiv H L X x)
    _ = (pointHomAlgEquiv H (IsLocalRing.ResidueField R) X
        (henselianSpecializationOverEquiv H R L X x)).comp (sectionsAlgHom H f) :=
      congrArg (fun z => z.comp (sectionsAlgHom H f))
        (pointHomAlgEquiv_henselianSpecializationOverEquiv H R L X x).symm
    _ = _ := (pointHomAlgEquiv_naturality H (IsLocalRing.ResidueField R) f _).symm

/-- The actual over-point specialization commutes with compatible automorphisms. -/
theorem henselianSpecializationOverEquiv_equivariant
    (τ : R ≃ₐ[H] R) (σ : L ≃ₐ[H] L)
    (hσ : ∀ r : R, σ (algebraMap R L r) = algebraMap R L (τ r))
    (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H L) ⟶ X.toComma) :
    henselianSpecializationOverEquiv H R L X (mapPointHom H L σ X x) =
      mapPointHom H (IsLocalRing.ResidueField R) (SchemeTheory.residueAlgEquiv H R τ) X
        (henselianSpecializationOverEquiv H R L X x) := by
  apply (pointHomAlgEquiv H (IsLocalRing.ResidueField R) X).injective
  calc
    _ = SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
        (pointHomAlgEquiv H L X (mapPointHom H L σ X x)) :=
      pointHomAlgEquiv_henselianSpecializationOverEquiv H R L X _
    _ = SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
        (σ.toAlgHom.comp (pointHomAlgEquiv H L X x)) :=
      congrArg (SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤))
        (pointHomAlgEquiv_mapPointHom H L σ X x)
    _ = (SchemeTheory.residueAlgEquiv H R τ).toAlgHom.comp
        (SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
          (pointHomAlgEquiv H L X x)) :=
      SchemeTheory.finiteEtalePointSpecialization_equivariant H R L Γ(X.left, ⊤)
        τ σ hσ (pointHomAlgEquiv H L X x)
    _ = (SchemeTheory.residueAlgEquiv H R τ).toAlgHom.comp
        (pointHomAlgEquiv H (IsLocalRing.ResidueField R) X
          (henselianSpecializationOverEquiv H R L X x)) :=
      congrArg (fun z => (SchemeTheory.residueAlgEquiv H R τ).toAlgHom.comp z)
        (pointHomAlgEquiv_henselianSpecializationOverEquiv H R L X x).symm
    _ = _ := (pointHomAlgEquiv_mapPointHom H (IsLocalRing.ResidueField R)
      (SchemeTheory.residueAlgEquiv H R τ) X _).symm

variable [IsSepClosed L] [IsSepClosed (IsLocalRing.ResidueField R)]

/-- The actual generic and residue fibers have the canonical specialization bijection. -/
def henselianSpecializationFiberEquiv (X : FiniteEtale (Spec (.of H))) :
    (fiber (Spec.algebraMap H L)).obj X ≃
      (fiber (Spec.algebraMap H (IsLocalRing.ResidueField R))).obj X :=
  (fiberObjEquivHom (Spec.algebraMap H L) X).trans
    ((henselianSpecializationOverEquiv H R L X).trans
      (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X).symm)

/-- The fiber comparison retains the actual over-point specialization. -/
theorem fiberObjEquivHom_henselianSpecializationFiberEquiv
    (X : FiniteEtale (Spec (.of H))) (x : (fiber (Spec.algebraMap H L)).obj X) :
    fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) X
        (henselianSpecializationFiberEquiv H R L X x) =
      henselianSpecializationOverEquiv H R L X
        (fiberObjEquivHom (Spec.algebraMap H L) X x) :=
  Equiv.apply_symm_apply _ _

/-- The canonical specialization identifies the two actual geometric fiber functors. -/
def henselianSpecializationFiberIso :
    fiber (Spec.algebraMap H L) ≅
      fiber (Spec.algebraMap H (IsLocalRing.ResidueField R)) :=
  NatIso.ofComponents
    (fun X => FintypeCat.equivEquivIso (henselianSpecializationFiberEquiv H R L X))
    (fun {X Y} f => by
      ext x
      change henselianSpecializationFiberEquiv H R L Y
          ((fiber (Spec.algebraMap H L)).map f x) =
        (fiber (Spec.algebraMap H (IsLocalRing.ResidueField R))).map f
          (henselianSpecializationFiberEquiv H R L X x)
      apply (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField R)) Y).injective
      rw [fiberObjEquivHom_henselianSpecializationFiberEquiv,
        ← fiberObjEquivHom_naturality]
      rw [← fiberObjEquivHom_naturality,
        fiberObjEquivHom_henselianSpecializationFiberEquiv]
      exact henselianSpecializationOverEquiv_naturality H R L f
        (fiberObjEquivHom (Spec.algebraMap H L) X x))

/-- This base-point comparison on fundamental groups comes from actual specialization. -/
def henselianSpecializationFundamentalGroupEquiv :
    π₁ᵉᵗ(Spec.algebraMap H L) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap H (IsLocalRing.ResidueField R)) :=
  fundamentalGroupIsoOfFiberIso _ _ (henselianSpecializationFiberIso H R L)

end AlgebraicGeometry.FiniteEtale
