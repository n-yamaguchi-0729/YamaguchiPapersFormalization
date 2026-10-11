/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryHenselization
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The ordinary henselization fraction field in the original ambient field

The native fraction-ring lift extends the actual injective ordinary-stalk
map. Localization extensionality extends the proved decomposition-group
fixedness to this actual fraction-field embedding.
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

/-- The actual fraction-ring map extending the original ordinary-stalk
embedding into the original ambient field. -/
def ordinaryHenselizationFractionToNormalizationField :
    FractionRing (ordinaryHenselization A) →+* L := by
  let j := ordinaryHenselizationToNormalizationField A K L Q hQ
  have hj : Function.Injective j :=
    ordinaryHenselizationToNormalizationField_injective A K L Q hQ
  have : IsDomain (ordinaryHenselization A) := hj.isDomain j
  exact IsFractionRing.lift (K := FractionRing (ordinaryHenselization A)) hj

/-- The fraction-ring map extends the literal ordinary-stalk map. -/
theorem ordinaryHenselizationFractionToNormalizationField_comp_stalk :
    (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).comp
      (algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))) =
      ordinaryHenselizationToNormalizationField A K L Q hQ := by
  let j := ordinaryHenselizationToNormalizationField A K L Q hQ
  have hj : Function.Injective j :=
    ordinaryHenselizationToNormalizationField_injective A K L Q hQ
  have : IsDomain (ordinaryHenselization A) := hj.isDomain j
  apply RingHom.ext
  intro a
  exact IsFractionRing.lift_algebraMap
    (K := FractionRing (ordinaryHenselization A)) hj a

theorem ordinaryHenselizationFractionToNormalizationField_injective :
    Function.Injective (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) := by
  have : IsDomain (ordinaryHenselization A) :=
    (ordinaryHenselizationToNormalizationField_injective A K L Q hQ).isDomain
      (ordinaryHenselizationToNormalizationField A K L Q hQ)
  exact (ordinaryHenselizationFractionToNormalizationField A K L Q hQ).injective

/-- The original decomposition group fixes the actual fraction-field
embedding of the ordinary henselization. -/
theorem ordinaryHenselizationFractionToNormalizationField_comp_decomposition
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    (σ : Gal(L/K)).toRingHom.comp
        (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) =
      ordinaryHenselizationFractionToNormalizationField A K L Q hQ := by
  let j := ordinaryHenselizationToNormalizationField A K L Q hQ
  let q := ordinaryHenselizationFractionToNormalizationField A K L Q hQ
  let a := algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))
  have hq : q.comp a = j :=
    ordinaryHenselizationFractionToNormalizationField_comp_stalk A K L Q hQ
  apply IsLocalization.ringHom_ext (nonZeroDivisors (ordinaryHenselization A))
  calc
    ((σ : Gal(L/K)).toRingHom.comp q).comp a =
        (σ : Gal(L/K)).toRingHom.comp (q.comp a) := RingHom.comp_assoc _ _ _
    _ = (σ : Gal(L/K)).toRingHom.comp j :=
      congrArg (RingHom.comp (σ : Gal(L/K)).toRingHom) hq
    _ = j := ordinaryHenselizationToNormalizationField_comp_decomposition A K L Q hQ σ
    _ = q.comp a := hq.symm

/-- The image of the actual ordinary fraction field lies in the original
decomposition fixed field. The reverse inclusion remains separate. -/
theorem ordinaryHenselizationFractionToNormalizationField_range_subset_fixedField :
    Set.range (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) ⊆
      (IntermediateField.fixedField (MulAction.stabilizer Gal(L/K) Q) : Set L) := by
  rintro x ⟨a, rfl⟩
  apply (IntermediateField.mem_fixedField_iff (MulAction.stabilizer Gal(L/K) Q) _).mpr
  intro σ hσ
  exact RingHom.congr_fun
    (ordinaryHenselizationFractionToNormalizationField_comp_decomposition A K L Q hQ
      ⟨σ, hσ⟩) a

end EtaleFundamentalGroups.StrictHenselian
