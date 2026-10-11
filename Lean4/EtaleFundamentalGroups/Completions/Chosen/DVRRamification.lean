/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Chosen.DVRProductCoordinate
import EtaleFundamentalGroups.Ramification.Product.Coordinate

/-!
# Ramification in the chosen completed DVR factor

The product decomposition of the completed finite model identifies the closed
prime selected from `Q` with the maximal ideal in the `Q`-coordinate.  This
file combines that identification with flat base-change invariance of
ramification to compare the completed local DVR directly with the original
normalization prime.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uV uC uK uL

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]

/-- The maximal ideal of the completed local DVR selected by `Q` has the
same ramification index as `Q` over the original DVR. -/
theorem completedPrimeValuationSubring_ramificationIdx_eq
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let A := completedPrimeValuationSubring (L := L) Q
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : Algebra Vhat A :=
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q
    (IsLocalRing.maximalIdeal A).ramificationIdx Vhat =
      Q.1.ramificationIdx V := by
  classical
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : IsLocalHom (algebraMap V Vhat) :=
    standardDVRToCompletion_isLocalHom V K
  let : Module.FaithfullyFlat V Vhat :=
    standardDVRCompletionValuationSubring_faithfullyFlat
      (V := V) (K := K)
  let U := Vhat ⊗[V] C
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let E := completedDVRIntegralExtensionLocalFactorsRingEquiv
    (V := V) (C := C) (K := K) (L := L)
  let P := completedBaseChangeChosenPrime
    (R := V) (R' := Vhat) Q.1
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  have hPmap :=
    (completedBaseChangeChosenPrimes_map_localFactors
      (V := V) (C := C) (K := K) (L := L) Q).1
  have hP : ringEquivProductCoordinatePrime A Q E = P := by
    change (productCoordinatePrime A Q).comap E.toRingHom = P
    rw [← hPmap, Ideal.comap_map_of_bijective E.toRingHom E.bijective]
  have hcoordinate :=
    ringEquivProductCoordinatePrime_ramificationIdx_eq
      (R := Vhat) A E Q
  have hbase := completedBaseChangeChosenPrime_ramificationIdx_eq
    (R := V) (R' := Vhat) hmax hres Q.1
  calc
    (IsLocalRing.maximalIdeal (A Q)).ramificationIdx Vhat =
        (ringEquivProductCoordinatePrime A Q E).ramificationIdx Vhat :=
      hcoordinate.symm
    _ = P.ramificationIdx Vhat := by rw [hP]
    _ = Q.1.ramificationIdx V := hbase

private theorem maximalIdeal_ramificationIdx_eq_of_algEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [IsLocalRing S] [IsLocalRing T]
    (e : S ≃ₐ[R] T) :
    (IsLocalRing.maximalIdeal S).ramificationIdx R =
      (IsLocalRing.maximalIdeal T).ramificationIdx R := by
  let : Algebra S T := e.toRingEquiv.toRingHom.toAlgebra
  let : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let eS : S ≃ₐ[S] T :=
    AlgEquiv.ofRingEquiv (R := S) (f := e.toRingEquiv) fun _ => rfl
  let : IsLocalization (IsUnit.submonoid S) T :=
    IsLocalization.isLocalization_of_algEquiv (IsUnit.submonoid S) eS
  have hdisj : Disjoint
      ((IsUnit.submonoid S : Submonoid S) : Set S)
      (IsLocalRing.maximalIdeal S : Set S) := by
    rw [Set.disjoint_left]
    intro x hxunit hxmax
    exact ((IsLocalRing.mem_maximalIdeal x).mp hxmax) hxunit
  have hram := ramificationIdx_map_eq_of_isLocalization
    (R := R) (S := S) (R' := R) (S' := T)
    (IsUnit.submonoid R) (IsUnit.submonoid S)
    (IsLocalRing.maximalIdeal S) hdisj
  have hmap : (IsLocalRing.maximalIdeal S).map (algebraMap S T) =
      IsLocalRing.maximalIdeal T := by
    change (IsLocalRing.maximalIdeal S).map e.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal T
    exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv
  rw [hmap] at hram
  exact hram.symm

section ChosenTensorNormalization

variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- The chosen normalization equivalence sends its maximal ideal to the
maximal ideal of the completed local DVR at `Q`. -/
theorem completedGenericTensorChosenIntegralClosureAlgEquiv_map_maximalIdeal
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    let A := fun Q' : (IsLocalRing.maximalIdeal V).primesOver C =>
      completedPrimeValuationSubring (L := L) Q'
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
    letI : SMul K Khat :=
      (standardDVFCompletionAlgebra V K).toSMul
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    letI : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    letI : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q'
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let B := integralClosure Vhat (GenericTensorFieldComponent m)
    let e := completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := V) (C := C) (K := K) (L := L) Q
    letI : IsLocalRing B := e.symm.toRingEquiv.isLocalRing
    (IsLocalRing.maximalIdeal B).map e.toRingEquiv.toRingHom =
      IsLocalRing.maximalIdeal (A Q) := by
  classical
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
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
  let : SMul K Khat :=
    (standardDVFCompletionAlgebra V K).toSMul
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let m := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  let B := integralClosure Vhat (GenericTensorFieldComponent m)
  let e := completedGenericTensorChosenIntegralClosureAlgEquiv
    (V := V) (C := C) (K := K) (L := L) Q
  let : IsLocalRing B := e.symm.toRingEquiv.isLocalRing
  exact IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv

/-- The maximal ideal in the normalization of the chosen completed generic
component has the original ramification index at `Q`. -/
theorem completedGenericTensorChosenIntegralClosure_ramificationIdx_eq
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    let A := fun Q' : (IsLocalRing.maximalIdeal V).primesOver C =>
      completedPrimeValuationSubring (L := L) Q'
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
    letI : SMul K Khat :=
      (standardDVFCompletionAlgebra V K).toSMul
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    letI : IsScalarTower V K Khat :=
      standardDVFCompletion_isScalarTower (V := V) (K := K)
    letI : IsScalarTower V Vhat Khat :=
      standardDVRCompletionValuationSubring_isScalarTower
        (V := V) (K := K)
    letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q'
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let m := completedGenericTensorChosenIdeal
      (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
      hmax hres Q.1
    let B := integralClosure Vhat (GenericTensorFieldComponent m)
    let e := completedGenericTensorChosenIntegralClosureAlgEquiv
      (V := V) (C := C) (K := K) (L := L) Q
    letI : IsLocalRing B := e.symm.toRingEquiv.isLocalRing
    (IsLocalRing.maximalIdeal B).ramificationIdx Vhat =
      Q.1.ramificationIdx V := by
  classical
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
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
  let : SMul K Khat :=
    (standardDVFCompletionAlgebra V K).toSMul
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  let : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  let : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let m := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  let B := integralClosure Vhat (GenericTensorFieldComponent m)
  let e := completedGenericTensorChosenIntegralClosureAlgEquiv
    (V := V) (C := C) (K := K) (L := L) Q
  let : IsLocalRing B := e.symm.toRingEquiv.isLocalRing
  calc
    (IsLocalRing.maximalIdeal B).ramificationIdx Vhat =
        (IsLocalRing.maximalIdeal (A Q)).ramificationIdx Vhat :=
      maximalIdeal_ramificationIdx_eq_of_algEquiv e
    _ = Q.1.ramificationIdx V :=
      completedPrimeValuationSubring_ramificationIdx_eq
        (V := V) (C := C) (K := K) (L := L) Q

end ChosenTensorNormalization

end EtaleFundamentalGroups

end
