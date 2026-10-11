/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryFieldTower
import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import EtaleFundamentalGroups.GeometricFiber.TransportedFieldSourcePoint
import EtaleFundamentalGroups.GeometricFiber.HenselianSpecializationConjugacy

/-!
# The actual ordinary generic-point map on the original decomposition group

The proved fixedness of the actual ordinary fraction-field embedding turns
each original decomposition automorphism into the same relative field
automorphism. The native generic-point scheme morphism then gives the actual
map to the ordinary-henselization fundamental group. Its point action is the
original ambient automorphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The original decomposition automorphism as an automorphism over the actual
ordinary fraction field, with its underlying ambient map unchanged. -/
def normalizationDecompositionOrdinaryFractionHom :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    (normalizationDecompositionGroup A K L Q).carrier →*
      Gal(L/FractionRing (ordinaryHenselization A)) := by
  intro actualDomain actualFractionAlgebra
  refine
    { toFun := fun d => by
        refine { d.val.toRingEquiv with commutes' := ?_ }
        intro x
        exact RingHom.congr_fun
          (ordinaryHenselizationFractionToNormalizationField_comp_decomposition
            A K L Q hQ d) x
      map_one' := ?_
      map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro x
    rfl
  · intro d e
    apply AlgEquiv.ext
    intro x
    rfl

/-- Relative scalar restriction keeps exactly the original ambient ring map. -/
theorem normalizationDecompositionOrdinaryFractionHom_toRingHom :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    ∀ d : (normalizationDecompositionGroup A K L Q).carrier,
      (normalizationDecompositionOrdinaryFractionHom A K L Q hQ d).toRingHom =
        d.val.toRingHom := by
  intro actualDomain actualFractionAlgebra d
  rfl

/-- The original ordinary fraction coefficient equation gives the literal
geometric-point triangle. -/
theorem normalizationOrdinaryGenericPoint_comp :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ξ (FractionRing (ordinaryHenselization A)) L ≫
        Spec.algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A)) =
      Spec.algebraMap (ordinaryHenselization A) L := by
  intro actualDomain actualFractionAlgebra actualAmbientAlgebra
  exact (Spec.map_comp
    (CommRingCat.ofHom (algebraMap (ordinaryHenselization A)
      (FractionRing (ordinaryHenselization A))))
    (CommRingCat.ofHom (algebraMap (FractionRing (ordinaryHenselization A)) L))).symm.trans
      (congrArg (fun r : ordinaryHenselization A →+* L => Spec.map (CommRingCat.ofHom r))
        (ordinaryHenselizationFractionToNormalizationField_comp_stalk A K L Q hQ))

/-- The literal generic-point image of the original decomposition group,
transported only along the proved equality of the actual field-valued points. -/
def normalizationOrdinaryGenericGaloisMap :
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    (normalizationDecompositionGroup A K L Q).carrier →*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) := by
  intro actualAmbientAlgebra
  let H := ordinaryHenselization A
  have : IsDomain H := geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  let E := FractionRing H
  let : Algebra K E := (ordinaryHenselizationFractionBaseMap A K).toAlgebra
  let : Algebra E L := (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
  have : IsScalarTower K E L := ordinaryHenselizationFractionField_isScalarTower A K L Q hQ
  have : IsSepClosure E L := ordinaryHenselizationFractionField_isSepClosure A K L Q hQ
  let j : Spec (.of E) ⟶ Spec (.of H) := Spec.algebraMap H E
  have hpoint : ξ E L ≫ j = Spec.algebraMap H L :=
    normalizationOrdinaryGenericPoint_comp A K L Q hQ
  let t : fiber (ξ E L ≫ j) ≅ fiber (Spec.algebraMap H L) :=
    eqToIso (congrArg fiber hpoint)
  exact (CategoryTheory.PreGaloisCategory.continuousConjAut t).toMonoidHom.comp
    ((fieldSourceAbsoluteGaloisHom E L j).toMonoidHom.comp
      (normalizationDecompositionOrdinaryFractionHom A K L Q hQ))

/-- Keep the actual generic map computation as an equality of automorphisms,
before projecting to a component of the concrete geometric fiber. -/
theorem normalizationOrdinaryGenericGaloisMap_apply :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let E := FractionRing (ordinaryHenselization A)
    let : Algebra K E := (ordinaryHenselizationFractionBaseMap A K).toAlgebra
    let : Algebra E L := (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    let : IsScalarTower K E L := ordinaryHenselizationFractionField_isScalarTower A K L Q hQ
    let : IsSepClosure E L := ordinaryHenselizationFractionField_isSepClosure A K L Q hQ
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ∀ d : (normalizationDecompositionGroup A K L Q).carrier,
      normalizationOrdinaryGenericGaloisMap A K L Q hQ d =
        CategoryTheory.PreGaloisCategory.continuousConjAut
          (eqToIso (congrArg fiber (normalizationOrdinaryGenericPoint_comp A K L Q hQ)))
          (fieldSourceAbsoluteGaloisHom E L (Spec.algebraMap (ordinaryHenselization A) E)
            (normalizationDecompositionOrdinaryFractionHom A K L Q hQ d)) := by
  intro actualDomain E actualBaseAlgebra actualFractionAlgebra actualTower actualSepClosure
    actualAmbientAlgebra d
  rfl

/-- On every finite étale point, the actual generic-point group map is
precomposition by the original ambient decomposition automorphism. -/
theorem normalizationOrdinaryGenericGaloisMap_point :
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ∀ (d : (normalizationDecompositionGroup A K L Q).carrier)
      (X : FiniteEtale (Spec (ordinaryHenselization A)))
      (x : (fiber (Spec.algebraMap (ordinaryHenselization A) L)).obj X),
      (fiberObjEquivHom (Spec.algebraMap (ordinaryHenselization A) L) X
        ((normalizationOrdinaryGenericGaloisMap A K L Q hQ d).hom.app X x)).left =
        Spec.map (CommRingCat.ofHom d.val.toRingHom) ≫
          (fiberObjEquivHom (Spec.algebraMap (ordinaryHenselization A) L) X x).left := by
  intro actualAmbientAlgebra d X x
  let H := ordinaryHenselization A
  have : IsDomain H := geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  let E := FractionRing H
  let : Algebra K E := (ordinaryHenselizationFractionBaseMap A K).toAlgebra
  let : Algebra E L := (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
  have : IsScalarTower K E L := ordinaryHenselizationFractionField_isScalarTower A K L Q hQ
  have : IsSepClosure E L := ordinaryHenselizationFractionField_isSepClosure A K L Q hQ
  let j : Spec (.of E) ⟶ Spec (.of H) := Spec.algebraMap H E
  have hpoint : ξ E L ≫ j = Spec.algebraMap H L :=
    normalizationOrdinaryGenericPoint_comp A K L Q hQ
  let τ := normalizationDecompositionOrdinaryFractionHom A K L Q hQ d
  exact transportedFieldSourceAbsoluteGaloisHom_point E L j (Spec.algebraMap H L) hpoint
    τ d.val.toRingHom (normalizationDecompositionOrdinaryFractionHom_toRingHom A K L Q hQ d)
    (normalizationOrdinaryGenericGaloisMap A K L Q hQ d)
    (normalizationOrdinaryGenericGaloisMap_apply A K L Q hQ d) X x

end EtaleFundamentalGroups.StrictHenselian
