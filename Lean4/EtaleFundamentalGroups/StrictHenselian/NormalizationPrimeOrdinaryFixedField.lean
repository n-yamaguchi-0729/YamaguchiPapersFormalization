/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryDecomposition
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual ordinary fraction image is the original decomposition fixed field

The actual fraction-ring image contains the original base fraction field:
write a base-field element as a quotient of original base-ring elements and
use the proved coefficient square. Hence the image is an actual intermediate
field of the original extension. Its proved fixing subgroup is the original
decomposition subgroup, so the native infinite Galois correspondence identifies
that same image with the decomposition fixed field.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The range of the actual ordinary fraction map as an intermediate field
of the original `L/K`. Containment of `K` is proved from original fractions. -/
def ordinaryHenselizationFractionImage : IntermediateField K L := by
  have : IsDomain (ordinaryHenselization A) :=
    (ordinaryHenselizationToNormalizationField_injective A K L Q hQ).isDomain
      (ordinaryHenselizationToNormalizationField A K L Q hQ)
  let q := ordinaryHenselizationFractionToNormalizationField A K L Q hQ
  have hbase (a : A) : algebraMap A L a ∈ q.fieldRange := by
    refine ⟨algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))
      (ordinaryHenselizationMap A a), ?_⟩
    exact (RingHom.congr_fun
      (ordinaryHenselizationFractionToNormalizationField_comp_stalk A K L Q hQ)
      (ordinaryHenselizationMap A a)).trans
        (RingHom.congr_fun (ordinaryHenselizationToNormalizationField_comp_map A K L Q hQ) a)
  refine { q.fieldRange with algebraMap_mem' := ?_ }
  intro k
  obtain ⟨a, b, _, hk⟩ := IsFractionRing.div_surjective A k
  have hkL : algebraMap K L k = algebraMap A L a / algebraMap A L b := by
    let ι : K →+* L := algebraMap K L
    exact (congrArg ι hk.symm).trans
      ((map_div₀ ι (algebraMap A K a) (algebraMap A K b)).trans
        (congrArg₂ (fun x y : L => x / y)
          (IsScalarTower.algebraMap_apply A K L a).symm
          (IsScalarTower.algebraMap_apply A K L b).symm))
  rw [hkL]
  exact q.fieldRange.div_mem (hbase a) (hbase b)

/-- The intermediate-field carrier is literally the actual fraction-map range. -/
theorem ordinaryHenselizationFractionImage_coe :
    (ordinaryHenselizationFractionImage A K L Q hQ : Set L) =
      Set.range (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) := rfl

/-- The image of the actual ordinary henselization fraction field is exactly
the field fixed by the original normalization-prime decomposition subgroup. -/
theorem ordinaryHenselizationFractionToNormalizationField_range_eq_fixedField :
    Set.range (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) =
      (IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) Q) : Set L) := by
  let E := ordinaryHenselizationFractionImage A K L Q hQ
  have hD : E.fixingSubgroup = MulAction.stabilizer Gal(L/K) Q :=
    ordinaryHenselizationFractionToNormalizationField_fixingSubgroup A K L Q hQ
  have hE : IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) Q) = E :=
    (congrArg IntermediateField.fixedField hD.symm).trans
      (InfiniteGalois.fixedField_fixingSubgroup E)
  exact (ordinaryHenselizationFractionImage_coe A K L Q hQ).symm.trans
    (congrArg (fun F : IntermediateField K L => (F : Set L)) hE).symm

/-- Bundled subring form of the literal actual-image equality. -/
theorem ordinaryHenselizationFractionToNormalizationField_ringRange_eq_fixedField :
    (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).range =
      (IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) Q)).toSubalgebra.toSubring := by
  apply Subring.ext
  intro x
  exact Iff.of_eq (congrArg (fun s : Set L => x ∈ s)
    (ordinaryHenselizationFractionToNormalizationField_range_eq_fixedField A K L Q hQ))

end EtaleFundamentalGroups.StrictHenselian
