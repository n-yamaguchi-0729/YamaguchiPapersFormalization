/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationAction
import Nyll.EtaleFundamentalGroups.Inertia.AffineNormalizationFunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.SchemeTheory.FunctionFields.Functoriality
import Nyll.SchemeTheory.Normalization.Normal

/-!
# The actual function-field normalization of an affine normal scheme

The source's global sections are a normal domain. Normalizing in those
sections or in their function field therefore gives the same scheme. The
algebra on the function field is constructed from the actual structure
morphism, and the induced action agrees with geometric pullback on rational
functions. All comparisons use the same section and function-field maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

variable (R : Type u) [CommRing R] {A : Scheme.{u}} [IsIntegral A]

/-- The function-field algebra supplied by an actual morphism to `Spec R`. -/
@[instance_reducible] def affineMorphismFunctionFieldAlgebra
    (f : A ⟶ Spec (.of R)) : Algebra R A.functionField := by
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  exact ((algebraMap Γ(A, ⊤) A.functionField).comp
    (algebraMap R Γ(A, ⊤))).toAlgebra

variable [IsAffine A]

/-- The field automorphism obtained by extending the actual coordinate action. -/
def affineMorphismFunctionFieldAlgEquiv
    (f : A ⟶ Spec (.of R)) (sigma : A ≅ A)
    (hsigma : sigma.hom ≫ f = f) :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    A.functionField ≃ₐ[R] A.functionField := by
  intro hRL
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  have : IsScalarTower R Γ(A, ⊤) A.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Nonempty (⊤ : A.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty A), trivial⟩⟩
  have : IsFractionRing Γ(A, ⊤) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A ⊤ (isAffineOpen_top A)
  exact IsFractionRing.algEquivOfAlgEquiv
    (affineMorphismAlgEquiv R f sigma hsigma)

/-- The fraction-field extension is exactly the pullback on rational functions
of the geometric automorphism; no compatibility is assumed. -/
theorem affineMorphismFunctionFieldAlgEquiv_eq_functionFieldMap
    (f : A ⟶ Spec (.of R)) (sigma : A ≅ A)
    (hsigma : sigma.hom ≫ f = f) :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    (affineMorphismFunctionFieldAlgEquiv R f sigma hsigma).toRingHom =
      sigma.hom.functionFieldMap sigma.hom.surjective.denseRange := by
  intro hRL
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  have : IsScalarTower R Γ(A, ⊤) A.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Nonempty (⊤ : A.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty A), trivial⟩⟩
  have : IsFractionRing Γ(A, ⊤) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A ⊤ (isAffineOpen_top A)
  apply IsFractionRing.ringHom_ext (A := Γ(A, ⊤))
  intro a
  have h := DFunLike.congr_fun (sigma.hom.functionFieldMap_comp_germToFunctionField_top
    sigma.hom.surjective.denseRange) a
  exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (K := A.functionField) (L := A.functionField)
    (affineMorphismAlgEquiv R f sigma hsigma) a).trans h.symm

variable [IsNormalIntegral A]

/-- The actual relative normalization of a normal affine source is the
spectrum of the integral closure in its actual function field. -/
def affineMorphismFunctionFieldNormalizationIso
    (f : A ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f] :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    f.normalization ≅ Spec (.of (integralClosure R A.functionField)) := by
  intro hRL
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  have : IsScalarTower R Γ(A, ⊤) A.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Nonempty (⊤ : A.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty A), trivial⟩⟩
  have : IsFractionRing Γ(A, ⊤) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A ⊤ (isAffineOpen_top A)
  have : IsIntegrallyClosed Γ(A, ⊤) :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top A)
  exact affineMorphismNormalizationIso R f ≪≫
    affineNormalizationFunctionFieldIso R Γ(A, ⊤) A.functionField

/-- The normalization isomorphism is over the original affine base. -/
@[reassoc]
theorem affineMorphismFunctionFieldNormalizationIso_hom_base
    (f : A ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f] :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    (affineMorphismFunctionFieldNormalizationIso R f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R A.functionField))) =
      f.fromNormalization := by
  intro hRL
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  have : IsScalarTower R Γ(A, ⊤) A.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Nonempty (⊤ : A.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty A), trivial⟩⟩
  have : IsFractionRing Γ(A, ⊤) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A ⊤ (isAffineOpen_top A)
  have : IsIntegrallyClosed Γ(A, ⊤) :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top A)
  dsimp only [affineMorphismFunctionFieldNormalizationIso, Iso.trans_hom]
  rw [Category.assoc, affineNormalizationFunctionFieldIso_hom_structureMap]
  exact normalizationSourceIso_hom_fromNormalization f
    (Spec.map (CommRingCat.ofHom (algebraMap R Γ(A, ⊤)))) A.isoSpec
    (isoSpec_affineMorphismAlgebra R f)

/-- The constructed normalization comparison preserves the geometric point's
fixed condition for the literal function-field action. -/
theorem affineMorphismFunctionFieldNormalizationIso_fixes_iff
    (f : A ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (sigma : A ≅ A) (hsigma : sigma.hom ≫ f = f)
    {T : Scheme.{u}} (z : T ⟶ f.normalization) :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    (z ≫ (affineMorphismFunctionFieldNormalizationIso R f).hom) ≫
        Spec.map (CommRingCat.ofHom
          (affineMorphismFunctionFieldAlgEquiv R f sigma
            hsigma).toAlgHom.mapIntegralClosure.toRingHom) =
      z ≫ (affineMorphismFunctionFieldNormalizationIso R f).hom ↔
        z ≫ normalizationEndomorphism f sigma.hom hsigma = z := by
  intro hRL
  let : Algebra R Γ(A, ⊤) := affineMorphismAlgebra R f
  let : Algebra Γ(A, ⊤) A.functionField := topSectionFunctionFieldAlgebra A
  have : IsScalarTower R Γ(A, ⊤) A.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : Nonempty (⊤ : A.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty A), trivial⟩⟩
  have : IsFractionRing Γ(A, ⊤) A.functionField :=
    functionField_isFractionRing_of_isAffineOpen A ⊤ (isAffineOpen_top A)
  have : IsIntegrallyClosed Γ(A, ⊤) :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top A)
  let zB := z ≫ (affineMorphismNormalizationIso R f).hom
  have hCoordinate := affineMorphismNormalizationIso_fixes_iff R f sigma hsigma z
  have hField :
      (zB ≫ (affineNormalizationFunctionFieldIso R Γ(A, ⊤) A.functionField).hom) ≫
          Spec.map (CommRingCat.ofHom
            (affineMorphismFunctionFieldAlgEquiv R f sigma
              hsigma).toAlgHom.mapIntegralClosure.toRingHom) =
        zB ≫ (affineNormalizationFunctionFieldIso R Γ(A, ⊤) A.functionField).hom ↔
      zB ≫ affineNormalizationDeck R Γ(A, ⊤)
          (affineMorphismAlgEquiv R f sigma hsigma) = zB := by
    rw [← cancel_mono (affineNormalizationFunctionFieldIso R Γ(A, ⊤) A.functionField).hom]
    simp only [Category.assoc, affineNormalizationDeck_affineNormalizationFunctionFieldIso,
      affineMorphismFunctionFieldAlgEquiv]
  have h := hField.trans hCoordinate
  simpa only [affineMorphismFunctionFieldNormalizationIso, Iso.trans_hom,
    zB, Category.assoc] using h

/-- Every actual geometric point of the relative normalization determines a
prime kernel in the integral closure, and its stabilizer is exactly ideal
inertia for the actual function-field automorphisms. -/
theorem exists_affineMorphismFunctionField_point_inertia_iff
    (f : A ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ f.normalization) :
    let : Algebra R A.functionField := affineMorphismFunctionFieldAlgebra R f
    ∃ φ : integralClosure R A.functionField →+* Ω,
      Spec.map (CommRingCat.ofHom φ) =
          z ≫ (affineMorphismFunctionFieldNormalizationIso R f).hom ∧
        ∀ (sigma : A ≅ A) (hsigma : sigma.hom ≫ f = f),
          let : MulSemiringAction (A.functionField ≃ₐ[R] A.functionField)
              (integralClosure R A.functionField) :=
            integralClosureAutAction R A.functionField
          affineMorphismFunctionFieldAlgEquiv R f sigma hsigma ∈
              (RingHom.ker φ).inertia (A.functionField ≃ₐ[R] A.functionField) ↔
            z ≫ normalizationEndomorphism f sigma.hom hsigma = z := by
  intro hRL
  let φ := (Spec.preimage
    (z ≫ (affineMorphismFunctionFieldNormalizationIso R f).hom)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) =
      z ≫ (affineMorphismFunctionFieldNormalizationIso R f).hom :=
    Spec.map_preimage _
  refine ⟨φ, hφ, ?_⟩
  intro sigma hsigma hAction
  have h := mem_idealInertia_iff_fixes_affineGeometricPoint
    (A.functionField ≃ₐ[R] A.functionField) φ
    (affineMorphismFunctionFieldAlgEquiv R f sigma hsigma)
  rw [hφ] at h
  exact h.trans (affineMorphismFunctionFieldNormalizationIso_fixes_iff
    R f sigma hsigma z)

end EtaleFundamentalGroups.Inertia
