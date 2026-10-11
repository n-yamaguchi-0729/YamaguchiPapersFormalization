/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFraction
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual original-field, stalk-fraction and ambient-field tower

The injective original stalk structure map induces its fraction-field map
from the displayed original K. The computed extension equation proves that
the actual ambient embedding composes to the original K-to-L map. Thus the
canonical algebras attached to these two constructed maps form a genuine
scalar tower. Fraction-field uniqueness also compares this map with the
existing canonical FractionRing A map used by the normal-local pi1 sequence.
-/

noncomputable section

open AlgebraicGeometry
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

/-- The actual normalization residue point is local over a local base,
using contraction of the original maximal normalization prime. -/
theorem normalizationResiduePoint_isLocalHom
    (A L : Type u) [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] :
    IsLocalHom ((IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)) := by
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
  infer_instance

variable (A : Type u) (K : Type v) (L : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal]

/-- The actual field map from the displayed original fraction field to
the fraction field of the constructed geometric stalk. -/
def normalizationStalkFractionBaseMap :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    K →+* FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q))))) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  have : IsLocalHom ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) :=
    normalizationResiduePoint_isLocalHom A L Q
  exact IsFractionRing.map
    (geometricStalkStructureMap_injective ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)))

/-- The displayed fraction-field map extends the actual original stalk
structure map on each coefficient of A. -/
theorem normalizationStalkFractionBaseMap_algebraMap (a : A) :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    normalizationStalkFractionBaseMap A K L Q (algebraMap A K a) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q))))))
        (geometricStalkStructureMap ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) a) := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  have : IsLocalHom ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) :=
    normalizationResiduePoint_isLocalHom A L Q
  exact IsLocalization.map_eq
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (geometricStalkStructureMap ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)))
      (geometricStalkStructureMap_injective ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)))) a

/-- The two actual field maps compose to the original K-to-L coefficient
map. This is proved on A and extended by fraction-field uniqueness. -/
theorem geometricStalkFractionToNormalizationField_comp_baseField :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    (geometricStalkFractionToNormalizationField A L Q).comp
        (normalizationStalkFractionBaseMap A K L Q) = algebraMap K L := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  exact (congrArg (geometricStalkFractionToNormalizationField A L Q)
    (normalizationStalkFractionBaseMap_algebraMap A K L Q a)).trans
      ((RingHom.congr_fun
        (geometricStalkFractionToNormalizationField_comp_stalk A K L Q)
        (geometricStalkStructureMap ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) a)).trans
          ((congrArg (integralClosurePrimeToAmbientField A K L Q)
            (RingHom.congr_fun
              (geometricStalkToHenselian_comp_structure (integralClosurePrimeBaseMap A L Q))
              a)).trans
                ((RingHom.congr_fun
                  (integralClosurePrimeToAmbientField_comp_baseMap A K L Q) a).trans
                    (IsScalarTower.algebraMap_apply A K L a))))

/-- The algebras of the two actual maps form a scalar tower with the
original K-action on L. No compatibility premise is introduced. -/
theorem normalizationStalkFractionField_isScalarTower :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : Algebra K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) :=
      (normalizationStalkFractionBaseMap A K L Q).toAlgebra
    let : Algebra (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L :=
      (geometricStalkFractionToNormalizationField A L Q).toAlgebra
    IsScalarTower K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
    actualBaseAlgebra actualAmbientAlgebra
  exact IsScalarTower.of_algebraMap_eq'
    (geometricStalkFractionToNormalizationField_comp_baseField A K L Q).symm

/-- The original separably closed Galois field is a separable closure of
the actual stalk fraction field for its constructed ambient action. -/
theorem normalizationStalkFractionField_isSepClosure :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : Algebra K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) :=
      (normalizationStalkFractionBaseMap A K L Q).toAlgebra
    let : Algebra (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L :=
      (geometricStalkFractionToNormalizationField A L Q).toAlgebra
    let : IsScalarTower K (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L :=
      normalizationStalkFractionField_isScalarTower A K L Q
    IsSepClosure (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed
    actualBaseAlgebra actualAmbientAlgebra actualTower
  exact ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K
    (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime Q)).comp
          (integralClosurePrimeBaseMap A L Q)))))) L⟩

/-- The displayed-field map is the existing canonical fraction-field map
precomposed with the proved original fraction-field equivalence. This keeps
an independent-universe K while allowing the canonical same-universe pi1 API. -/
theorem normalizationStalkFractionBaseMap_eq_canonical :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let : IsLocalHom ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) :=
      normalizationResiduePoint_isLocalHom A L Q
    normalizationStalkFractionBaseMap A K L Q =
      (geometricStalkFractionFieldMap ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q))).comp
        (IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)).toRingHom := by
  intro actualAlgebraic actualFaithful actualHenselian actualSepClosed actualLocal
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  exact (normalizationStalkFractionBaseMap_algebraMap A K L Q a).trans
    ((congrArg (geometricStalkFractionFieldMap ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)))
      ((IsLocalization.algEquiv (nonZeroDivisors A) K (FractionRing A)).commutes a)).trans
        (geometricStalkFractionFieldMap_algebraMap
          ((IsLocalRing.residue (Localization.AtPrime Q)).comp
        (integralClosurePrimeBaseMap A L Q)) a)).symm

end EtaleFundamentalGroups.StrictHenselian
