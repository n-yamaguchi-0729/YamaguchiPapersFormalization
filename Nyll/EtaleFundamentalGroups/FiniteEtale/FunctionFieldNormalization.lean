/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.FractionField
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv

/-!
# Normalization in the function field of a finite-etale cover

For a connected finite-etale cover `Y ⟶ X` of an affine normal integral
scheme, the integral closure of `Γ(X, ⊤)` in the function field of `Y` is
finite etale over `Γ(X, ⊤)`.  The algebra structures are the canonical ones
coming from global sections, germs at the generic points, and the
function-field map of the cover.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- The canonical algebra structure on a scheme's function field coming
from germs of global sections. -/
@[reducible] noncomputable def topSectionFunctionFieldAlgebra
    (Z : Scheme.{u}) [IsIntegral Z] :
    Algebra Γ(Z, ⊤) Z.functionField := by
  letI : Nonempty (⊤ : Z.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Z), trivial⟩⟩
  exact (Z.germToFunctionField ⊤).hom.toAlgebra

/-- The canonical `Γ(X, ⊤)`-algebra structure on the function field of a
connected finite-etale cover.  It is the composite through the function
field of `X`. -/
@[reducible] noncomputable def finiteEtaleSectionFunctionFieldAlgebra
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    Algebra Γ(X, ⊤) Y.left.functionField := by
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  letI : Algebra Γ(X, ⊤) X.functionField :=
    topSectionFunctionFieldAlgebra X
  letI : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  exact ((algebraMap X.functionField Y.left.functionField).comp
    (X.germToFunctionField ⊤).hom).toAlgebra

/-- The two canonical maps from `Γ(X, ⊤)` to the function field of a
connected finite-etale cover agree: one factors through `Γ(Y, ⊤)`, the
other through the function field of `X`. -/
theorem finiteEtale_sectionFunctionField_isScalarTower
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra Γ(X, ⊤) Γ(Y.left, ⊤) :=
      Y.hom.appTop.hom.toAlgebra
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra Γ(Y.left, ⊤) Y.left.functionField :=
      topSectionFunctionFieldAlgebra Y.left
    letI : Algebra Γ(X, ⊤) Y.left.functionField :=
      finiteEtaleSectionFunctionFieldAlgebra Y
    IsScalarTower Γ(X, ⊤) Γ(Y.left, ⊤) Y.left.functionField := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let f : Y.left ⟶ X := Y.hom
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  let : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  let : Algebra Γ(X, ⊤) Γ(Y.left, ⊤) :=
    f.appTop.hom.toAlgebra
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : Algebra Γ(Y.left, ⊤) Y.left.functionField :=
    topSectionFunctionFieldAlgebra Y.left
  let : Algebra Γ(X, ⊤) Y.left.functionField :=
    finiteEtaleSectionFunctionFieldAlgebra Y
  apply IsScalarTower.of_algebraMap_eq'
  exact Scheme.Hom.functionFieldMap_comp_germToFunctionField_top f
    (finiteEtale_hom_denseRange_of_isConnected Y)

/-- For a connected finite-etale cover of an affine normal integral scheme,
the normalization of the base section ring in the cover's function field is
finite etale.

There is no Noetherian, finite-type, Nagata, or arithmetic-base assumption. -/
theorem integralClosure_functionField_etale_of_finiteEtale_isConnected
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsAffine X]
    (Y : FiniteEtale X) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra Γ(X, ⊤) Y.left.functionField :=
      finiteEtaleSectionFunctionFieldAlgebra Y
    Algebra.Etale Γ(X, ⊤)
      (integralClosure Γ(X, ⊤) Y.left.functionField) := by
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let f : Y.left ⟶ X := Y.hom
  let : IsFiniteEtale f := Y.2
  let : IsAffine Y.left := isAffine_of_isAffineHom f
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), trivial⟩⟩
  let : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  let R := Γ(X, ⊤)
  let T := Γ(Y.left, ⊤)
  let K := X.functionField
  let L := Y.left.functionField
  let : Algebra R T := f.appTop.hom.toAlgebra
  let : Module.Finite R T := by
    rw [← RingHom.finite_algebraMap]
    exact f.finite_appTop
  have hEtale : f.appTop.hom.Etale := by
    rw [← HasRingHomProperty.iff_of_isAffine
      (P := @AlgebraicGeometry.Etale)]
    exact Y.2.toEtale
  let : Algebra.Etale R T := hEtale.toAlgebra
  let : IsIntegrallyClosed R :=
    IsNormalIntegral.affine_isIntegrallyClosed ⊤ (isAffineOpen_top X)
  let : Algebra R K := topSectionFunctionFieldAlgebra X
  let : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  let : Algebra T L := topSectionFunctionFieldAlgebra Y.left
  let : IsFractionRing T L :=
    functionField_isFractionRing_of_isAffineOpen Y.left ⊤
      (isAffineOpen_top Y.left)
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R L := finiteEtaleSectionFunctionFieldAlgebra Y
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R T L :=
    finiteEtale_sectionFunctionField_isScalarTower Y
  exact integralClosure_etale_of_finiteEtale_fractionField
    (R := R) (T := T) (K := K) (L := L)

/-- The canonical algebra structure on the function field of a connected
finite-etale cover of `Spec R`, written over the literal ring `R`. -/
@[reducible] noncomputable def finiteEtaleSpecFunctionFieldAlgebra
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    Algebra R Y.left.functionField := by
  let X := Spec R
  letI : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  letI : Algebra Γ(X, ⊤) Y.left.functionField :=
    finiteEtaleSectionFunctionFieldAlgebra Y
  exact ((algebraMap Γ(X, ⊤) Y.left.functionField).comp
    (Scheme.ΓSpecIso R).inv.hom).toAlgebra

/-- The literal `R`-algebra structure on the function field of a connected
finite-etale cover of `Spec R` factors through the function field of
`Spec R`. -/
theorem finiteEtaleSpec_functionField_isScalarTower
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra (Spec R).functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra R Y.left.functionField :=
      finiteEtaleSpecFunctionFieldAlgebra R Y
    IsScalarTower R (Spec R).functionField Y.left.functionField := by
  let X := Spec R
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : Algebra R Y.left.functionField :=
    finiteEtaleSpecFunctionFieldAlgebra R Y
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- Literal affine form of
`integralClosure_functionField_etale_of_finiteEtale_isConnected`.

For a connected finite-etale cover of `Spec R`, the integral closure of the
literal normal domain `R` in the cover's function field is finite
etale over `R`. -/
theorem integralClosure_functionField_etale_of_finiteEtale_spec
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra (Spec R).functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra R Y.left.functionField :=
      finiteEtaleSpecFunctionFieldAlgebra R Y
    Algebra.Etale R (integralClosure R Y.left.functionField) := by
  let X := Spec R
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : Algebra Γ(X, ⊤) Y.left.functionField :=
    finiteEtaleSectionFunctionFieldAlgebra Y
  let : Algebra R Y.left.functionField :=
    finiteEtaleSpecFunctionFieldAlgebra R Y
  have hΓ : Algebra.Etale Γ(X, ⊤)
      (integralClosure Γ(X, ⊤) Y.left.functionField) :=
    integralClosure_functionField_etale_of_finiteEtale_isConnected Y
  let e : R ≃+* Γ(X, ⊤) :=
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have he : (algebraMap Γ(X, ⊤) Y.left.functionField).comp e.toRingHom =
      algebraMap R Y.left.functionField := rfl
  exact integralClosure_etale_of_baseRingEquiv e he hΓ

end EtaleFundamentalGroups
