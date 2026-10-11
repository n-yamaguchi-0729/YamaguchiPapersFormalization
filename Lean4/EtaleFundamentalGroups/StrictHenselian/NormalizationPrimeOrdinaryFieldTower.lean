/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselization
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryFraction
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The original base field and actual ordinary-henselization fraction field

The native fraction map of the original local structure map supplies the
displayed `K → Frac(H)`. Its composite with the actual embedding in `L` is
the original coefficient map, proved on `A` and extended by fraction-field
uniqueness. The resulting scalar tower makes the original separably closed
Galois field a separable closure of the actual ordinary fraction field.
-/

noncomputable section

open AlgebraicGeometry
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

section Base

variable (A : Type u) (K : Type v)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]

/-- The actual original fraction field maps to the actual fraction field of
the ordinary henselization by the native localization map. -/
def ordinaryHenselizationFractionBaseMap : K →+* FractionRing (ordinaryHenselization A) := by
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  exact IsFractionRing.map (K := K) (L := FractionRing (ordinaryHenselization A))
    (show Function.Injective (ordinaryHenselizationMap A) from
      geometricStalkStructureMap_injective (IsLocalRing.residue A))

theorem ordinaryHenselizationFractionBaseMap_algebraMap (a : A) :
    ordinaryHenselizationFractionBaseMap A K (algebraMap A K a) =
      algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))
        (ordinaryHenselizationMap A a) := by
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  exact IsLocalization.map_eq
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (ordinaryHenselizationMap A)
      (geometricStalkStructureMap_injective (IsLocalRing.residue A))) a

/-- The displayed-field map uses the same canonical fraction map already
attached to the existing pointed-stalk construction. -/
theorem ordinaryHenselizationFractionBaseMap_eq_canonical :
    ordinaryHenselizationFractionBaseMap A K =
      (geometricStalkFractionFieldMap (IsLocalRing.residue A)).comp
        (IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)).toRingHom := by
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  let f₁ : K →+* FractionRing (ordinaryHenselization A) :=
    ordinaryHenselizationFractionBaseMap A K
  let f₂ : K →+* FractionRing (ordinaryHenselization A) :=
    (geometricStalkFractionFieldMap (IsLocalRing.residue A)).comp
      (IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)).toRingHom
  have h : f₁ = f₂ := IsFractionRing.ringHom_ext (A := A) (K := K)
    (L := FractionRing (ordinaryHenselization A)) (f1 := f₁) (f2 := f₂) (fun a =>
      (ordinaryHenselizationFractionBaseMap_algebraMap A K a).trans
        ((congrArg (geometricStalkFractionFieldMap (IsLocalRing.residue A))
          ((IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)).commutes a)).trans
            (geometricStalkFractionFieldMap_algebraMap (IsLocalRing.residue A) a)).symm)
  exact h

end Base

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The actual ordinary fraction embedding preserves the displayed original
fraction-field coefficient map, with no compatibility assumption. -/
theorem ordinaryHenselizationFractionToNormalizationField_comp_baseField :
    (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).comp
      (ordinaryHenselizationFractionBaseMap A K) = algebraMap K L := by
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  exact (congrArg (ordinaryHenselizationFractionToNormalizationField A K L Q hQ)
    (ordinaryHenselizationFractionBaseMap_algebraMap A K a)).trans
      ((RingHom.congr_fun
        (ordinaryHenselizationFractionToNormalizationField_comp_stalk A K L Q hQ)
        (ordinaryHenselizationMap A a)).trans
          ((RingHom.congr_fun
            (ordinaryHenselizationToNormalizationField_comp_map A K L Q hQ) a).trans
              (IsScalarTower.algebraMap_apply A K L a)))

theorem ordinaryHenselizationFractionField_isScalarTower :
    let : Algebra K (FractionRing (ordinaryHenselization A)) :=
      (ordinaryHenselizationFractionBaseMap A K).toAlgebra
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    IsScalarTower K (FractionRing (ordinaryHenselization A)) L := by
  intro actualBaseAlgebra actualAmbientAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (ordinaryHenselizationFractionToNormalizationField_comp_baseField A K L Q hQ).symm

/-- The original ambient field is a separable closure for the actual
ordinary fraction-field action obtained from the original normalization. -/
theorem ordinaryHenselizationFractionField_isSepClosure :
    let : IsDomain (ordinaryHenselization A) :=
      geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
    let : Algebra K (FractionRing (ordinaryHenselization A)) :=
      (ordinaryHenselizationFractionBaseMap A K).toAlgebra
    let : Algebra (FractionRing (ordinaryHenselization A)) L :=
      (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).toAlgebra
    let : IsScalarTower K (FractionRing (ordinaryHenselization A)) L :=
      ordinaryHenselizationFractionField_isScalarTower A K L Q hQ
    IsSepClosure (FractionRing (ordinaryHenselization A)) L := by
  intro actualDomain actualBaseAlgebra actualAmbientAlgebra actualTower
  exact ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K
    (FractionRing (ordinaryHenselization A)) L⟩

end EtaleFundamentalGroups.StrictHenselian
