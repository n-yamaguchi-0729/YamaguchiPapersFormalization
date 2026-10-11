/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Henselian.PointedEtale
import EtaleFundamentalGroups.Kummer.Completions.NormalizationPrime.ExactTensorTarget

/-!
# The exact completed normalization prime is the chosen DVR factor

The completed tensor product may have several factors, so it must not be
identified with one localization.  Once a factor `Q` and the corresponding
generic component have been fixed, however, the normalization of that
component is canonically the complete DVR factor selected by `Q`.

That normalization is local.  Consequently every specified maximal prime in
it is its literal maximal ideal, and localization at that same prime recovers
the chosen complete DVR factor.  This is the same-prime comparison needed by
the exact tensor-coordinate package.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uV uC uK uL

/-- Localization at a maximal prime of the chosen completed component
normalization is canonically the complete DVR factor selected by `Q`.

The theorem compares only the already selected factor; it does not assert an
equivalence between the whole completed tensor product and a local ring. -/
noncomputable def
    completedGenericTensorChosenNormalizationPrimeLocalizationAlgEquiv
    {V : Type uV} {C : Type uC} {K : Type uK} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C]
    [Algebra V C] [Algebra.IsIntegral V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra K L] [IsScalarTower V K L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : IsLocalHom (algebraMap V Vhat) :=
      standardDVRToCompletion_isLocalHom V K
    letI : Module.FaithfullyFlat V Vhat :=
      standardDVRCompletionValuationSubring_faithfullyFlat
        (V := V) (K := K)
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
    letI : Algebra V Khat :=
      standardDVFCompletionBaseAlgebra (V := V) (K := K)
    letI : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    letI : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    letI : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let M := GenericTensorFieldComponent m
    let IC := integralClosure Vhat M
    let A := completedPrimeValuationSubring (L := L) Q
    letI : Algebra Vhat A :=
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q
    ∀ (q : Ideal IC), [q.IsMaximal] →
      let D := Localization.AtPrime q
      letI : SMul IC D := OreLocalization.instSMulOfIsScalarTower
      letI : Algebra Vhat D := OreLocalization.instAlgebra
      D ≃ₐ[Vhat] A := by
  intro H Vhat Khat hmax hres m M IC A
  letI : CommRing IC := inferInstance
  letI : Algebra Vhat A :=
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q
  let eIC : IC ≃ₐ[Vhat] A :=
    completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := V) (C := C) (K := K) (L := L) Q
  letI : IsLocalRing IC := eIC.symm.toRingEquiv.isLocalRing
  intro q hqMax D
  have hq : q = IsLocalRing.maximalIdeal IC :=
    IsLocalRing.eq_maximalIdeal hqMax
  subst q
  letI : SMul IC D := OreLocalization.instSMulOfIsScalarTower
  letI : Algebra Vhat D := OreLocalization.instAlgebra
  letI : IsScalarTower Vhat IC D :=
    OreLocalization.instIsScalarTower
  let eLocal : IC ≃ₐ[IC] D :=
    localizationAtMaximalIdealAlgEquiv IC
  let eLocalVhat : IC ≃ₐ[Vhat] D :=
    { toRingEquiv := eLocal.toRingEquiv
      commutes' := by
        intro z
        rw [IsScalarTower.algebraMap_apply Vhat IC D]
        exact eLocal.commutes (algebraMap Vhat IC z) }
  exact eLocalVhat.symm.trans eIC

end EtaleFundamentalGroups.Kummer

end
