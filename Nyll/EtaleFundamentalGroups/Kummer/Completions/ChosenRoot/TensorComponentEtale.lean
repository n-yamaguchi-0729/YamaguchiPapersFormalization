/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Chosen.GenericComponentTarget
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.TowerIdealOver
import Nyll.EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualTensorTowerIntermediate
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.RootCompletionBaseChange
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Completion

/-!
# The prescribed completed root component selected by a normalization prime

A prime `Q` above the closed point of a DVR canonically selects a component
of the completed generic fibre.  We choose a post-root component above it,
equip the intermediate component with its canonical complete valuation, and
apply the arbitrary-exponent complete Abhyankar factor theorem.  The only
arithmetic hypothesis is the intrinsic divisibility `e(Q) ∣ N`.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uC uK uL

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- The normalization of a post-root component selected above `Q` is finite
etale over the prescribed completed root ring.  The component and its
maximality proof are returned as data. -/
theorem integralClosure_completedChosenRootTensorComponent_etale
    (Q : (IsLocalRing.maximalIdeal V).primesOver C)
    (pi : V)
    (hpi : IsLocalRing.maximalIdeal V = Ideal.span ({pi} : Set V))
    (N : ℕ) (hN : 0 < N)
    (hdiv : Q.1.ramificationIdx V ∣ N)
    (hCharZero : CharZero
      (V ⧸ IsLocalRing.maximalIdeal V)) :
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
    let varpiHat : Vhat :=
      standardDVRCompletionValuationSubringElement V K pi
    let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiHat)
    letI : IsDomain Rn :=
      completeDVFRootRing_isDomain H varpiHat
        (standardDVRCompletionValuationSubringElement_isUniformizer
          V K pi hpi) N hN
    let F := FractionRing Rn
    letI : Algebra Khat F :=
      completeDVFRootFractionFieldAlgebra H varpiHat
        (standardDVRCompletionValuationSubringElement_isUniformizer
          V K pi hpi) N hN
    letI : IsScalarTower Vhat Khat F :=
      completeDVFRootFractionField_isScalarTower H varpiHat
        (standardDVRCompletionValuationSubringElement_isUniformizer
          V K pi hpi) N hN
    letI : Algebra K F :=
      ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
    letI : IsScalarTower K Khat F :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : FiniteDimensional Khat F :=
      pureRadicalFractionField_finiteDimensional hN varpiHat
        (completeDVFUniformizer_prime H varpiHat
          (standardDVRCompletionValuationSubringElement_isUniformizer
            V K pi hpi))
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let n := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    ∃ m : Ideal (F ⊗[K] L), ∃ hm : m.IsMaximal,
      letI : m.IsMaximal := hm
      let P := GenericTensorFieldComponent m
      letI : Algebra Rn P :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Rn) m
      genericTensorTowerIntermediateIdeal
          (K := K) (F := Khat) (F' := F) (L := L) m = n ∧
        Algebra.Etale Rn (integralClosure Rn P) := by
  classical
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V Vhat) :=
    standardDVRToCompletion_isLocalHom V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat := (standardDVFCompletionAlgebra V K).toSMul
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let varpiHat : Vhat :=
    standardDVRCompletionValuationSubringElement V K pi
  have hvarpiHat : H.valuation.IsUniformizer (varpiHat : Khat) :=
    standardDVRCompletionValuationSubringElement_isUniformizer
      V K pi hpi
  let : CharZero H.residueField :=
    charZero_standardDVFCompletionCompleteDVF_residueField
      V K hCharZero
  let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiHat)
  let : IsDomain Rn :=
    completeDVFRootRing_isDomain H varpiHat hvarpiHat N hN
  let F := FractionRing Rn
  let : Algebra Khat F :=
    completeDVFRootFractionFieldAlgebra H varpiHat hvarpiHat N hN
  let : IsScalarTower Vhat Khat F :=
    completeDVFRootFractionField_isScalarTower
      H varpiHat hvarpiHat N hN
  let : Algebra K F :=
    ((algebraMap Khat F).comp (algebraMap K Khat)).toAlgebra
  let : IsScalarTower K Khat F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : FiniteDimensional Khat F :=
    pureRadicalFractionField_finiteDimensional hN varpiHat
      (completeDVFUniformizer_prime H varpiHat hvarpiHat)
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let n := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  let : n.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  let m := genericTensorTowerIdealOver
    (K := K) (F := Khat) (F' := F) (L := L) n
  let : m.IsMaximal := genericTensorTowerIdealOver_isMaximal
    (K := K) (F := Khat) (F' := F) (L := L) n
  have hmn : genericTensorTowerIntermediateIdeal
      (K := K) (F := Khat) (F' := F) (L := L) m = n :=
    genericTensorTowerIntermediateIdeal_idealOver
      (K := K) (F := Khat) (F' := F) (L := L) n
  refine ⟨m, inferInstance, hmn, ?_⟩
  have hTarget :
      ∃ target : CompleteDVF.{_, 0} (GenericTensorFieldComponent n),
        ∃ hExt : H.valuation.HasExtension target.valuation,
          letI : H.valuation.HasExtension target.valuation := hExt
          Module.Finite Vhat target.valuationSubring ∧
            ramificationIndex H.toDVF target.toDVF =
              Q.1.ramificationIdx V := by
    exact exists_completedChosenGenericComponent_completeDVF
      (V := V) (C := C) (K := K) (L := L) Q
  obtain ⟨target, hExt, hfinite, hram⟩ := hTarget
  let : H.valuation.HasExtension target.valuation := hExt
  let : Module.Finite Vhat target.valuationSubring := hfinite
  have hdivTarget : ramificationIndex H.toDVF target.toDVF ∣ N := by
    rw [hram]
    exact hdiv
  exact
    integralClosure_pureRadicalFractionField_fixedTensorComponent_etale_of_intermediateIdeal_eq
      H varpiHat hvarpiHat N hN m inferInstance n inferInstance hmn
        target hdivTarget

end EtaleFundamentalGroups.Kummer

end
