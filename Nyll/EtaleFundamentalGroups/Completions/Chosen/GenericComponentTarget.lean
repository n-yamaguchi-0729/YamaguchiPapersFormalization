/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Nyll.EtaleFundamentalGroups.Completions.Chosen.DVRRamification
import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.Complete
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.DVRLocalExtension
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtension

/-!
# A complete valued target for the chosen completed generic component

The completed product decomposition selects a finite complete DVR over the
completed base DVR.  Its fraction field is identified with the already chosen
generic tensor component; pulling the standard complete valuation back along
that identification produces the complete valued target used by the local
Abhyankar argument.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open ValuationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uV uC uK uL

/-- The original fraction-field component equivalence proves that the base acts
faithfully on the completed coordinate ring. -/
private theorem faithfulSMul_of_component_fraction_equiv
    (R : Type*) (B : Type*) (K₁ : Type*) (F₁ : Type*) (L₁ : Type*) [CommRing R] [CommRing B]
    [Field K₁] [Field F₁] [Field L₁]
    [Algebra R K₁] [IsFractionRing R K₁]
    [Algebra R B] [Algebra B F₁] [Algebra R F₁]
    [IsScalarTower R B F₁]
    [Algebra K₁ L₁] [Algebra R L₁] [IsScalarTower R K₁ L₁]
    (e : L₁ ≃ₐ[R] F₁) : FaithfulSMul R B := by
  refine (faithfulSMul_iff_algebraMap_injective R B).mpr ?_
  intro x y h
  apply IsFractionRing.injective R K₁
  apply (algebraMap K₁ L₁).injective
  apply e.injective
  calc
    e (algebraMap K₁ L₁ (algebraMap R K₁ x)) = algebraMap R F₁ x :=
      (congrArg e (IsScalarTower.algebraMap_apply R K₁ L₁ x).symm).trans (e.commutes x)
    _ = algebraMap B F₁ (algebraMap R B x) :=
      IsScalarTower.algebraMap_apply R B F₁ x
    _ = algebraMap B F₁ (algebraMap R B y) := congrArg (algebraMap B F₁) h
    _ = algebraMap R F₁ y := (IsScalarTower.algebraMap_apply R B F₁ y).symm
    _ = e (algebraMap K₁ L₁ (algebraMap R K₁ y)) :=
      ((congrArg e (IsScalarTower.algebraMap_apply R K₁ L₁ y).symm).trans
        (e.commutes y)).symm

/-- The already constructed component embedding and fraction-field equivalence
compute scalar compatibility of the inverse valuation-ring equivalence. -/
private theorem inverse_component_equiv_commutes
    (R : Type*) (A : Type*) (S : Type*) (L₁ : Type*) (F₁ : Type*)
    [CommRing R] [CommRing A] [CommRing S] [CommRing L₁] [CommRing F₁]
    [Algebra R A] [Algebra A F₁] [Algebra R F₁] [IsScalarTower R A F₁]
    [Algebra R L₁]
    (e : L₁ ≃ₐ[R] F₁) (r : S ≃+* A) (ι : S →+* L₁)
    (hr : ∀ x : S, algebraMap A F₁ (r x) = e (ι x)) (z : R) :
    ι (r.symm (algebraMap R A z)) = algebraMap R L₁ z := by
  apply e.injective
  calc
    e (ι (r.symm (algebraMap R A z))) =
        algebraMap A F₁ (r (r.symm (algebraMap R A z))) :=
      (hr (r.symm (algebraMap R A z))).symm
    _ = algebraMap A F₁ (algebraMap R A z) :=
      congrArg (algebraMap A F₁) (r.apply_symm_apply (algebraMap R A z))
    _ = algebraMap R F₁ z := (IsScalarTower.algebraMap_apply R A F₁ z).symm
    _ = e (algebraMap R L₁ z) := (e.commutes z).symm

/-- The ambient scalar identity of the inverse valuation-ring equivalence,
together with the canonical integer map, proves scalar compatibility of the
original ring equivalence. -/
private theorem valuationRingEquiv_commutes_of_inverse_coe
    (K₁ : Type*) (L₁ : Type*) (A₁ : Type*)
    [Field K₁] [Field L₁] [CommRing A₁] [Algebra K₁ L₁]
    (base : DVF K₁) (target : DVF L₁)
    [base.valuation.HasExtension target.valuation]
    [Algebra base.valuationSubring A₁]
    (r : target.valuationSubring ≃+* A₁)
    (hr : ∀ z : base.valuationSubring,
      ((r.symm (algebraMap base.valuationSubring A₁ z) :
        target.valuationSubring) : L₁) = algebraMap K₁ L₁ (z : K₁))
    (z : base.valuationSubring) :
    r (algebraMap base.valuationSubring target.valuationSubring z) =
      algebraMap base.valuationSubring A₁ z := by
  apply r.symm.injective
  refine (r.symm_apply_apply
    (algebraMap base.valuationSubring target.valuationSubring z)).trans ?_
  apply Subtype.ext
  exact (integerMap_apply base target z).trans (hr z).symm

variable {V : Type uV} {C : Type uC}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [CommRing C] [IsDedekindDomain C]
variable [Algebra V C] [Algebra.IsIntegral V C]
variable [Module.IsTorsionFree V C] [Module.Finite V C]
variable {K : Type uK} [Field K] [Algebra V K] [IsFractionRing V K]
variable {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]

/-- A completed local factor is finite over the completed base DVR for the
canonical coordinate algebra structure. -/
theorem completedPrimeValuationSubringCompletionAlgebra_finite
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let A := completedPrimeValuationSubring (L := L) Q
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : Algebra Vhat A :=
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q
    Module.Finite Vhat A := by
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let U := Vhat ⊗[V] C
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let : Module.Finite Vhat U := Module.Finite.base_change V Vhat C
  let E := completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
    (V := V) (C := C) (K := K) (L := L)
  let f : U →ₐ[Vhat] A Q := (Pi.evalAlgHom Vhat A Q).comp E.toAlgHom
  exact Module.Finite.of_surjective f.toLinearMap
    ((Pi.evalRingHom A Q).surjective.comp E.surjective)

section ChosenGenericComponent

variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- The generic tensor component selected by `Q` carries a complete discrete
valuation extending the completed base valuation.  Its valuation ring is
finite over the completed base DVR, and its ramification index is the
original ideal-theoretic ramification index at `Q`. -/
theorem exists_completedChosenGenericComponent_completeDVF
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
    let L₀ := GenericTensorFieldComponent m
    ∃ target : CompleteDVF.{_, 0} L₀,
      ∃ hExt : H.valuation.HasExtension target.valuation,
        letI : H.valuation.HasExtension target.valuation := hExt
        Module.Finite Vhat target.valuationSubring ∧
          ramificationIndex H.toDVF target.toDVF =
            Q.1.ramificationIdx V := by
  classical
  intro H Vhat Khat
  let p := IsLocalRing.maximalIdeal V
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
  let A := completedPrimeValuationSubring (L := L) Q
  let : Algebra Vhat A :=
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q
  let : Module.Finite Vhat A :=
    completedPrimeValuationSubringCompletionAlgebra_finite
      (V := V) (C := C) (K := K) (L := L) Q
  let : Algebra.IsIntegral Vhat A :=
    completedPrimeValuationSubringCompletionAlgebra_isIntegral
      (V := V) (C := C) (K := K) (L := L) Q
  intro hmax hres m
  let : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  intro L₀
  let F := FractionRing A
  let : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    dsimp only [A, completedPrimeValuationSubring]
    infer_instance
  let T₀ := standardCompleteDVFOfCompleteDVR A F
  let e : L₀ ≃ₐ[Vhat] F :=
    completedGenericTensorChosenComponentFractionRingAlgEquiv
      (V := V) (C := C) (K := K) (L := L) Q
  have hVhat_coe (z : Vhat) :
      algebraMap Vhat Khat z = (z : Khat) := rfl
  let : FaithfulSMul Vhat A :=
    faithfulSMul_of_component_fraction_equiv Vhat A Khat F L₀ e
  let : IsLocalHom (algebraMap Vhat A) := inferInstance
  let target : CompleteDVF.{_, 0} L₀ :=
    { ValueGroup := T₀.ValueGroup
      valuation := T₀.valuation.comap (e.toRingEquiv : L₀ →+* F)
      instCompleteDiscrete :=
        Valuation.isCompleteDiscrete_comap_ringEquiv
          T₀.valuation e.toRingEquiv }
  let eComap : target.valuationSubring ≃+* T₀.valuationSubring :=
    Valuation.valuationSubringRingEquivOfComap T₀.valuation e.toRingEquiv
  let eA : A ≃+* T₀.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := A) (K := F)
  let r : target.valuationSubring ≃+* A := eComap.trans eA.symm
  have hr_coe (x : target.valuationSubring) :
      algebraMap A F (r x) = e (x : L₀) := by
    calc
      algebraMap A F (r x) = (eA (r x) : F) :=
        (dvr_equivValuationSubring_coe (L := F) A (r x)).symm
      _ = (eA (eA.symm (eComap x)) : F) :=
        congrArg (fun y : A => (eA y : F))
          (RingEquiv.trans_apply eComap eA.symm x)
      _ = (eComap x : F) :=
        congrArg (fun y : T₀.valuationSubring => (y : F))
          (eA.apply_symm_apply (eComap x))
      _ = e (x : L₀) :=
        Valuation.valuationSubringRingEquivOfComap_apply T₀.valuation e.toRingEquiv x
  let f : Vhat →+* target.valuationSubring :=
    r.symm.toRingHom.comp (algebraMap Vhat A)
  let : IsLocalHom r.symm.toRingHom :=
    IsLocalHom.of_surjective r.symm.toRingHom r.symm.surjective
  let : IsLocalHom f :=
    RingHom.isLocalHom_comp r.symm.toRingHom (algebraMap Vhat A)
  have hf_coe (z : Vhat) :
      ((f z : target.valuationSubring) : L₀) =
        algebraMap Khat L₀ (z : Khat) := by
    change
      ((r.symm (algebraMap Vhat A z) : target.valuationSubring) : L₀) =
        algebraMap Khat L₀ (z : Khat)
    exact (inverse_component_equiv_commutes Vhat A target.valuationSubring L₀ F
      e r (ValuationSubring.subtype target.valuation.valuationSubring) hr_coe z).trans
        ((IsScalarTower.algebraMap_apply Vhat Khat L₀ z).trans
          (congrArg (algebraMap Khat L₀) (hVhat_coe z)))
  let hExt : H.valuation.HasExtension target.valuation :=
    valuation_hasExtension_of_local_valuationSubring_map
      H target f hf_coe
  refine ⟨target, hExt, ?_⟩
  let : H.valuation.HasExtension target.valuation := hExt
  let rAlg : target.valuationSubring ≃ₐ[Vhat] A :=
    AlgEquiv.ofRingEquiv (f := r)
      (valuationRingEquiv_commutes_of_inverse_coe Khat L₀ A
        H.toDVF target.toDVF r hf_coe)
  have hFiniteTarget : Module.Finite Vhat target.valuationSubring :=
    Module.Finite.equiv rAlg.symm.toLinearEquiv
  let : Module.Finite Vhat target.valuationSubring := hFiniteTarget
  refine ⟨hFiniteTarget, ?_⟩
  have htransport :=
    Ideal.ramificationIdx'_map_eq
      H.maximalIdeal target.maximalIdeal rAlg
  have hmap : Ideal.map rAlg target.maximalIdeal =
      IsLocalRing.maximalIdeal A := by
    exact IsLocalRing.map_ringEquiv_maximalIdeal rAlg.toRingEquiv
  rw [hmap] at htransport
  let : (IsLocalRing.maximalIdeal A).LiesOver H.maximalIdeal :=
    Ideal.LiesOver.mk
      (IsLocalRing.maximalIdeal_comap (algebraMap Vhat A)).symm
  have hA :
      H.maximalIdeal.ramificationIdx' (IsLocalRing.maximalIdeal A) =
        (IsLocalRing.maximalIdeal A).ramificationIdx Vhat :=
    Ideal.ramificationIdx'_eq_ramificationIdx
      H.maximalIdeal (IsLocalRing.maximalIdeal A)
        (IsDiscreteValuationRing.not_a_field Vhat)
  change H.maximalIdeal.ramificationIdx' target.maximalIdeal =
    Q.1.ramificationIdx V
  calc
    H.maximalIdeal.ramificationIdx' target.maximalIdeal =
        H.maximalIdeal.ramificationIdx' (IsLocalRing.maximalIdeal A) :=
      htransport.symm
    _ = (IsLocalRing.maximalIdeal A).ramificationIdx Vhat := hA
    _ = Q.1.ramificationIdx V := by
      exact completedPrimeValuationSubring_ramificationIdx_eq
        (V := V) (C := C) (K := K) (L := L) Q

end ChosenGenericComponent

end EtaleFundamentalGroups

end
