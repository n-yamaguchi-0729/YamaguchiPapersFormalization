/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Chosen.GenericComponent
import Nyll.EtaleFundamentalGroups.Completions.DVR.IntegralExtensionLocalFactors
import Nyll.SchemeTheory.RingTheory.GenericFiber.DVRProductComponent
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# The completed component selected by a normalization prime

For a finite Dedekind extension of a DVR, the completed tensor product is the
product of the completed local DVRs.  This file proves that the closed prime
and the generic prime selected from a fixed prime `Q` become, respectively,
the maximal ideal and the zero prime in the `Q`-coordinate.  Consequently the
generic tensor component selected from `Q` is the fraction field of that same
completed local DVR.
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

/-- The canonical map from a DVR to the valuation subring in its valued-field
completion is faithfully flat. -/
theorem standardDVRCompletionValuationSubring_faithfullyFlat :
    let H := standardDVFCompletionCompleteDVF V K
    letI : Algebra V H.valuationSubring :=
      standardDVFCompletionValuationSubringAlgebra V K
    Module.FaithfullyFlat V H.valuationSubring := by
  let H := standardDVFCompletionCompleteDVF V K
  let : Algebra V H.valuationSubring :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : Module.IsTorsionFree V H.valuationSubring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      intro x y hxy
      apply IsFractionRing.injective V K
      apply (standardDVFCompletionMap V K).injective
      calc
        standardDVFCompletionMap V K (algebraMap V K x) =
            ((algebraMap V H.valuationSubring x : H.valuationSubring) :
              standardDVFCompletionField V K) :=
          (coe_standardDVRToCompletionValuationSubringMap V K x).symm
        _ = ((algebraMap V H.valuationSubring y : H.valuationSubring) :
              standardDVFCompletionField V K) := congrArg Subtype.val hxy
        _ = standardDVFCompletionMap V K (algebraMap V K y) :=
          coe_standardDVRToCompletionValuationSubringMap V K y)
  let : Module.Flat V H.valuationSubring := inferInstance
  let : IsLocalHom (algebraMap V H.valuationSubring) :=
    standardDVRToCompletion_isLocalHom V K
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The `V`-algebra structure on the completed fraction field obtained by
composing the fraction-field embedding with the canonical completion map. -/
@[reducible]
noncomputable def standardDVFCompletionBaseAlgebra :
    Algebra V (standardDVFCompletionField V K) :=
  ((standardDVFCompletionMap V K).comp (algebraMap V K)).toAlgebra

/-- The two canonical maps from the original DVR to the completed field,
through its fraction field and through the completed valuation subring, agree.
-/
theorem standardDVRCompletionValuationSubring_isScalarTower :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let Khat := standardDVFCompletionField V K
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
    letI : Algebra V Khat :=
      standardDVFCompletionBaseAlgebra (V := V) (K := K)
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    IsScalarTower V Vhat Khat := by
  dsimp only
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let Khat := standardDVFCompletionField V K
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact coe_standardDVRToCompletionValuationSubringMap V K x

/-- The canonical fraction-field map followed by the completion map is the
canonical `V`-algebra structure on the completed field. -/
theorem standardDVFCompletion_isScalarTower :
    let Khat := standardDVFCompletionField V K
    letI : Algebra K Khat := standardDVFCompletionAlgebra V K
    letI : Algebra V Khat :=
      standardDVFCompletionBaseAlgebra (V := V) (K := K)
    letI : SMul K Khat :=
      (standardDVFCompletionAlgebra V K).toSMul
    letI : SMul V Khat :=
      (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
    IsScalarTower V K Khat := by
  dsimp only
  let Khat := standardDVFCompletionField V K
  let : Algebra K Khat := standardDVFCompletionAlgebra V K
  let : Algebra V Khat :=
    standardDVFCompletionBaseAlgebra (V := V) (K := K)
  let : SMul K Khat :=
    (standardDVFCompletionAlgebra V K).toSMul
  let : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

/-- The algebra structure on a completed local factor induced by its
coordinate in the completed product decomposition. -/
@[reducible]
noncomputable def completedPrimeValuationSubringCompletionAlgebra
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    Algebra Vhat (completedPrimeValuationSubring (L := L) Q) := by
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  letI : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let U := Vhat ⊗[V] C
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  letI : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let E := completedDVRIntegralExtensionLocalFactorsRingEquiv
    (V := V) (C := C) (K := K) (L := L)
  exact ((Pi.evalRingHom A Q).comp
    (E.toRingHom.comp (algebraMap Vhat U))).toAlgebra

/-- The completed local-factor decomposition as an algebra equivalence over
the completed base DVR. -/
noncomputable def completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv :
    let p := IsLocalRing.maximalIdeal V
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    let U := Vhat ⊗[V] C
    let A := fun Q' : p.primesOver C =>
      completedPrimeValuationSubring (L := L) Q'
    letI : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
    letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q'
    U ≃ₐ[Vhat] ∀ Q', A Q' := by
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  letI : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let U := Vhat ⊗[V] C
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  letI : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let E := completedDVRIntegralExtensionLocalFactorsRingEquiv
    (V := V) (C := C) (K := K) (L := L)
  exact AlgEquiv.ofRingEquiv (R := Vhat) (f := E) fun r => by
    funext Q
    rw [Pi.algebraMap_apply]
    change E (algebraMap Vhat U r) Q =
      ((Pi.evalRingHom A Q).comp
        (E.toRingHom.comp (algebraMap Vhat U))) r
    rfl

/-- Every completed local factor is integral over the completed base DVR for
the coordinate algebra structure. -/
theorem completedPrimeValuationSubringCompletionAlgebra_isIntegral
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let p := IsLocalRing.maximalIdeal V
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    let A := fun Q' : p.primesOver C =>
      completedPrimeValuationSubring (L := L) Q'
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
      completedPrimeValuationSubringCompletionAlgebra
        (V := V) (C := C) (K := K) (L := L) Q'
    Algebra.IsIntegral Vhat (A Q) := by
  let p := IsLocalRing.maximalIdeal V
  let H := standardDVFCompletionCompleteDVF V K
  let Vhat := H.valuationSubring
  let : Algebra V Vhat :=
    standardDVFCompletionValuationSubringAlgebra V K
  let U := Vhat ⊗[V] C
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  let : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  let : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let : Module.Finite Vhat U := Module.Finite.base_change V Vhat C
  let E := completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
    (V := V) (C := C) (K := K) (L := L)
  let f : U →ₐ[Vhat] A Q := (Pi.evalAlgHom Vhat A Q).comp E.toAlgHom
  let : Module.Finite Vhat (A Q) :=
    Module.Finite.of_surjective f.toLinearMap
      ((Pi.evalRingHom A Q).surjective.comp E.surjective)
  exact Algebra.IsIntegral.of_finite Vhat (A Q)

section GenericFiberTransport

universe uR uF uU uU'

variable {R₀ : Type uR} {F : Type uF} {U₀ : Type uU} {U₁ : Type uU'}
variable [CommRing R₀] [Field F] [Algebra R₀ F]
variable [CommRing U₀] [CommRing U₁] [Algebra R₀ U₀] [Algebra R₀ U₁]

/-- Transporting a generic-fibre ideal through an algebra equivalence
transports its contraction through the same equivalence. -/
theorem genericFiberComponentBaseIdeal_map_tensorProductCongr
    (e : U₀ ≃ₐ[R₀] U₁) (m : Ideal (F ⊗[R₀] U₀)) :
    let eG := Algebra.TensorProduct.congr
      (AlgEquiv.refl : F ≃ₐ[R₀] F) e
    genericFiberComponentBaseIdeal (m.map eG.toRingEquiv.toRingHom) =
      (genericFiberComponentBaseIdeal m).map e.toRingEquiv.toRingHom := by
  dsimp only
  let eG := Algebra.TensorProduct.congr
    (AlgEquiv.refl : F ≃ₐ[R₀] F) e
  unfold genericFiberComponentBaseIdeal
  change Ideal.comap
      (Algebra.TensorProduct.includeRight : U₁ →ₐ[R₀] F ⊗[R₀] U₁)
      (Ideal.map eG.toRingEquiv.toRingHom m) =
    Ideal.map e.toRingEquiv.toRingHom
      (Ideal.comap
        (Algebra.TensorProduct.includeRight : U₀ →ₐ[R₀] F ⊗[R₀] U₀) m)
  have hm : Ideal.map eG.toRingEquiv.toRingHom m =
      Ideal.comap eG.symm.toRingEquiv.toRingHom m :=
    Ideal.map_comap_of_equiv eG.toRingEquiv
  have hn : Ideal.map e.toRingEquiv.toRingHom
        (Ideal.comap
          (Algebra.TensorProduct.includeRight : U₀ →ₐ[R₀] F ⊗[R₀] U₀) m) =
      Ideal.comap e.symm.toRingEquiv.toRingHom
        (Ideal.comap
          (Algebra.TensorProduct.includeRight : U₀ →ₐ[R₀] F ⊗[R₀] U₀) m) :=
    Ideal.map_comap_of_equiv e.toRingEquiv
  rw [hm, hn]
  ext y
  change eG.symm (Algebra.TensorProduct.includeRight y) ∈ m ↔
    Algebra.TensorProduct.includeRight (e.symm y) ∈ m
  rw [← Algebra.TensorProduct.congr_symm]
  simp only [Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one]
  rfl

universe uι uA

/-- Transport a generic-fibre quotient through a product decomposition and
identify it with the fraction field of the coordinate selected by its kernel. -/
private noncomputable def genericFiberComponentFractionRingAlgEquivOfCoordinate
    {ι : Type uι} (A : ι → Type uA)
    [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
    [∀ j, IsDiscreteValuationRing (A j)] [∀ j, Algebra R₀ (A j)]
    [IsFractionRing R₀ F]
    (i : ι) (e : U₀ ≃ₐ[R₀] ∀ j, A j)
    (m : Ideal (F ⊗[R₀] U₀)) [m.IsMaximal]
    (hker : (genericFiberComponentBaseIdeal m).map e.toRingEquiv.toRingHom =
      RingHom.ker (Pi.evalRingHom A i)) :
    ((F ⊗[R₀] U₀) ⧸ m) ≃ₐ[R₀] FractionRing (A i) := by
  let eG := Algebra.TensorProduct.congr
    (AlgEquiv.refl : F ≃ₐ[R₀] F) e
  let mP := m.map eG.toRingEquiv.toRingHom
  let : mP.IsMaximal :=
    (inferInstance : m.IsMaximal).map_bijective
      (f := eG.toRingEquiv.toRingHom) eG.toRingEquiv.bijective
  have hcontract : genericFiberComponentBaseIdeal mP =
      RingHom.ker (Pi.evalRingHom A i) :=
    (genericFiberComponentBaseIdeal_map_tensorProductCongr e m).trans hker
  have hbelow : genericFiberComponentBaseIdeal mP ≤ productCoordinatePrime A i := by
    rw [hcontract]
    change (⊥ : Ideal (A i)).comap (Pi.evalRingHom A i) ≤
      (IsLocalRing.maximalIdeal (A i)).comap (Pi.evalRingHom A i)
    exact Ideal.comap_mono bot_le
  have hstrict : genericFiberComponentBaseIdeal mP ≠ productCoordinatePrime A i := by
    rw [hcontract]
    intro hEq
    have hbotmax : (⊥ : Ideal (A i)) = IsLocalRing.maximalIdeal (A i) :=
      (Ideal.comap_injective_of_surjective (Pi.evalRingHom A i)
        (Pi.evalRingHom A i).surjective) hEq
    exact Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal (A i))
      (IsDiscreteValuationRing.not_isField (A i)) hbotmax.symm
  let q : ((F ⊗[R₀] U₀) ⧸ m) ≃ₐ[R₀]
      ((F ⊗[R₀] (∀ j, A j)) ⧸ mP) :=
    Ideal.quotientEquivAlg m mP eG rfl
  exact q.trans
    (genericFiberDVRProductComponentFractionRingAlgEquiv A i mP hbelow hstrict)

end GenericFiberTransport

section IntegralClosureTransport

universe uR uA uM

variable {R₀ : Type uR} {A₀ : Type uA} {M₀ : Type uM}
variable [CommRing R₀] [CommRing A₀] [Field M₀]
variable [Algebra R₀ A₀] [Algebra R₀ M₀]
variable [Algebra.IsIntegral R₀ A₀] [IsIntegrallyClosed A₀]

/-- A fraction-field identification with an integrally closed integral
`R₀`-algebra identifies the normalization of `R₀` with that algebra. -/
noncomputable def integralClosureEquivOfFractionRingAlgEquiv
    (e : M₀ ≃ₐ[R₀] FractionRing A₀) :
    integralClosure R₀ M₀ ≃ₐ[R₀] A₀ := by
  let i : A₀ →+* M₀ := e.symm.toRingEquiv.toRingHom.comp
    (algebraMap A₀ (FractionRing A₀))
  letI : Algebra A₀ M₀ := i.toAlgebra
  letI : IsScalarTower R₀ A₀ M₀ := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    apply e.injective
    change e (algebraMap R₀ M₀ r) = e (i (algebraMap R₀ A₀ r))
    change e (algebraMap R₀ M₀ r) = e (e.symm
      (algebraMap A₀ (FractionRing A₀) (algebraMap R₀ A₀ r)))
    rw [e.apply_symm_apply, e.commutes]
    exact (IsScalarTower.algebraMap_apply
      R₀ A₀ (FractionRing A₀) r).symm
  let eA : FractionRing A₀ ≃ₐ[A₀] M₀ :=
    AlgEquiv.ofRingEquiv (f := e.symm.toRingEquiv) fun _ => rfl
  letI : IsFractionRing A₀ M₀ := IsFractionRing.of_algEquiv eA
  letI : IsIntegralClosure A₀ R₀ M₀ :=
    IsIntegralClosure.of_isIntegrallyClosed A₀ R₀ M₀
  exact IsIntegralClosure.equiv R₀ (integralClosure R₀ M₀) M₀ A₀

end IntegralClosureTransport

/-- Under the product decomposition of the completed finite model, the
closed and generic primes selected from `Q` become the `Q`-coordinate maximal
ideal and the kernel of `Q`-coordinate evaluation. -/
theorem completedBaseChangeChosenPrimes_map_localFactors
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    let H := standardDVFCompletionCompleteDVF V K
    let Vhat := H.valuationSubring
    letI : Algebra V Vhat :=
      standardDVFCompletionValuationSubringAlgebra V K
    letI : IsLocalHom (algebraMap V Vhat) :=
      standardDVRToCompletion_isLocalHom V K
    letI : Module.FaithfullyFlat V Vhat :=
      standardDVRCompletionValuationSubring_faithfullyFlat
        (V := V) (K := K)
    let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
    let hres := standardDVRToCompletion_residueFieldMap_bijective V K
    let E := completedDVRIntegralExtensionLocalFactorsRingEquiv
      (V := V) (C := C) (K := K) (L := L)
    let A := fun Q' : (IsLocalRing.maximalIdeal V).primesOver C =>
      completedPrimeValuationSubring (L := L) Q'
    let P := completedBaseChangeChosenPrime
      (R := V) (R' := Vhat) Q.1
    let N := completedBaseChangeChosenGenericPrime
      (R := V) (R' := Vhat) hmax hres Q.1
    P.map E.toRingHom = productCoordinatePrime A Q ∧
      N.map E.toRingHom = RingHom.ker (Pi.evalRingHom A Q) := by
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
  let : Algebra C U := Algebra.TensorProduct.rightAlgebra
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let E := completedDVRIntegralExtensionLocalFactorsRingEquiv
    (V := V) (C := C) (K := K) (L := L)
  let P := completedBaseChangeChosenPrime
    (R := V) (R' := Vhat) Q.1
  let N := completedBaseChangeChosenGenericPrime
    (R := V) (R' := Vhat) hmax hres Q.1
  have hcomponent :
      (Pi.evalRingHom A Q).comp
          (E.toRingHom.comp (algebraMap C U)) =
        completedPrimeMap (L := L) Q := by
    ext x
    have hx := completedDVRIntegralExtensionLocalFactorsRingEquiv_includeRight_apply
      (V := V) (C := C) (K := K) (L := L) x Q
    dsimp only at hx
    have hRight : (algebraMap C U) x =
        Algebra.TensorProduct.includeRight x := rfl
    calc
      ((Pi.evalRingHom A Q).comp
          (E.toRingHom.comp (algebraMap C U))) x =
          E ((algebraMap C U) x) Q := rfl
      _ = E (Algebra.TensorProduct.includeRight x) Q :=
        congrArg (fun u : U ↦ E u Q) hRight
      _ = completedPrimeMap (L := L) Q x := hx
  have hgeom := completedBaseChangeChosenPrime_isMaximal_liesOver
    (R := V) (R' := Vhat) hmax hres Q.1
  have hP_le : P ≤ (productCoordinatePrime A Q).comap E.toRingHom := by
    change Q.1.map (algebraMap C U) ≤
      (productCoordinatePrime A Q).comap E.toRingHom
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change E (algebraMap C U x) Q ∈
      IsLocalRing.maximalIdeal (A Q)
    change ((Pi.evalRingHom A Q).comp
      (E.toRingHom.comp (algebraMap C U))) x ∈
        IsLocalRing.maximalIdeal (A Q)
    rw [hcomponent]
    change x ∈ (IsLocalRing.maximalIdeal (A Q)).comap
      (completedPrimeMap (L := L) Q)
    rw [completedPrimeMap_comap_maximalIdeal]
    exact hx
  have hPcomap :
      P = (productCoordinatePrime A Q).comap E.toRingHom :=
    hgeom.1.eq_of_le
      (Ideal.comap_ne_top E.toRingHom
        (inferInstance : (productCoordinatePrime A Q).IsPrime).ne_top)
      hP_le
  have hPmap : P.map E.toRingHom = productCoordinatePrime A Q := by
    apply le_antisymm
    · exact (Ideal.map_le_iff_le_comap).2 hPcomap.le
    · intro y hy
      have hpre : E.symm y ∈ P := by
        rw [hPcomap]
        change E (E.symm y) ∈ productCoordinatePrime A Q
        simpa only [E.apply_symm_apply] using hy
      have himage : E (E.symm y) ∈ P.map E.toRingHom :=
        Ideal.mem_map_of_mem E.toRingHom hpre
      simpa only [E.apply_symm_apply] using himage
  have hNspec := completedBaseChangeChosenGenericPrime_spec
    (R := V) (R' := Vhat) hmax hres Q.1
  let : N.IsPrime := hNspec.2.1
  let : N.LiesOver (⊥ : Ideal Vhat) := hNspec.2.2
  let : P.LiesOver (IsLocalRing.maximalIdeal Vhat) := hgeom.2
  have hkerE : RingHom.ker E.toRingHom ≤ N := by
    have hker : RingHom.ker E.toRingHom = ⊥ :=
      (RingHom.ker_eq_bot_iff_eq_zero E.toRingHom).2 fun x hx =>
        E.injective (hx.trans E.toRingHom.map_zero.symm)
    rw [hker]
    exact bot_le
  let : (N.map E.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_surjective E.surjective hkerE
  have hNP : N.map E.toRingHom ≤ productCoordinatePrime A Q := by
    rw [← hPmap]
    exact Ideal.map_mono hNspec.1
  have hNneP : N ≠ P := by
    intro hNP'
    have hbotmax : (⊥ : Ideal Vhat) = IsLocalRing.maximalIdeal Vhat := by
      calc
        (⊥ : Ideal Vhat) = N.under Vhat := N.over_def (⊥ : Ideal Vhat)
        _ = P.under Vhat := by rw [hNP']
        _ = IsLocalRing.maximalIdeal Vhat :=
          (P.over_def (IsLocalRing.maximalIdeal Vhat)).symm
    have hmaxne : IsLocalRing.maximalIdeal Vhat ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField
        (IsLocalRing.maximalIdeal.isMaximal Vhat)
        (IsDiscreteValuationRing.not_isField Vhat)
    exact hmaxne hbotmax.symm
  have hNne : N.map E.toRingHom ≠ productCoordinatePrime A Q := by
    intro hmap
    apply hNneP
    apply (Ideal.relIsoOfBijective E.toRingHom E.bijective).symm.injective
    exact hmap.trans hPmap.symm
  exact ⟨hPmap,
    prime_eq_ker_coordinateEval_of_le_of_ne A Q
      (N.map E.toRingHom) hNP hNne⟩

section ChosenTensorComponent

variable [Algebra V L] [IsScalarTower V C L]
variable [Algebra K L] [IsScalarTower V K L]

/-- The generic tensor component selected by `Q` is the fraction field of
the completed local DVR at that same `Q`.  The equivalence is over the
completed base valuation subring. -/
noncomputable def completedGenericTensorChosenComponentFractionRingAlgEquiv
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
    GenericTensorFieldComponent m ≃ₐ[Vhat] FractionRing (A Q) := by
  classical
  let p := IsLocalRing.maximalIdeal V
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
  letI : SMul K Khat :=
    (standardDVFCompletionAlgebra V K).toSMul
  letI : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  letI : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  letI : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let U := Vhat ⊗[V] C
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  letI : Algebra Vhat U := Algebra.TensorProduct.leftAlgebra
  letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  let E := completedDVRIntegralExtensionLocalFactorsCompletionAlgEquiv
    (V := V) (C := C) (K := K) (L := L)
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let N := completedBaseChangeChosenGenericPrime
    (R := V) (R' := Vhat) hmax hres Q.1
  let m₀ := completedBaseChangeChosenGenericIdeal
    (R := V) (R' := Vhat) (K' := Khat) hmax hres Q.1
  let m := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  letI : m₀.IsMaximal := completedBaseChangeChosenGenericIdeal_isMaximal
    (R := V) (R' := Vhat) (K' := Khat) hmax hres Q.1
  have hcontract₀ : genericFiberComponentBaseIdeal m₀ = N := by
    have h := completedBaseChangeChosenGenericIdeal_comap
      (R := V) (R' := Vhat) (K' := Khat) hmax hres Q.1
    dsimp only at h
    exact h
  have hprimeSpec := completedBaseChangeChosenPrimes_map_localFactors
    (V := V) (C := C) (K := K) (L := L) Q
  dsimp only at hprimeSpec
  let qProduct : ((Khat ⊗[Vhat] U) ⧸ m₀) ≃ₐ[Vhat] FractionRing (A Q) :=
    genericFiberComponentFractionRingAlgEquivOfCoordinate A Q E m₀ (by
      rw [hcontract₀]
      exact hprimeSpec.2)
  let eOriginal := completedGenericFiberEquiv
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
  have hmOriginal :
      m = m₀.map eOriginal.toRingEquiv.toRingHom := by
    dsimp only [m, m₀, eOriginal, completedGenericTensorChosenIdeal]
  let qOriginalKhat :
      ((Khat ⊗[Vhat] U) ⧸ m₀) ≃ₐ[Khat]
        GenericTensorFieldComponent m :=
    Ideal.quotientEquivAlg m₀ m eOriginal hmOriginal
  let qOriginal :
      ((Khat ⊗[Vhat] U) ⧸ m₀) ≃ₐ[Vhat]
        GenericTensorFieldComponent m :=
    qOriginalKhat.restrictScalars Vhat
  exact qOriginal.symm.trans qProduct

/-- The normalization of the completed base DVR in the generic tensor
component selected by `Q` is the completed local DVR at `Q`. -/
noncomputable def completedGenericTensorChosenIntegralClosureAlgEquiv
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
    integralClosure Vhat (GenericTensorFieldComponent m) ≃ₐ[Vhat] A Q := by
  classical
  let p := IsLocalRing.maximalIdeal V
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
  letI : SMul K Khat :=
    (standardDVFCompletionAlgebra V K).toSMul
  letI : SMul V Khat :=
    (standardDVFCompletionBaseAlgebra (V := V) (K := K)).toSMul
  letI : IsScalarTower V K Khat :=
    standardDVFCompletion_isScalarTower (V := V) (K := K)
  letI : IsScalarTower V Vhat Khat :=
    standardDVRCompletionValuationSubring_isScalarTower
      (V := V) (K := K)
  let A := fun Q' : p.primesOver C =>
    completedPrimeValuationSubring (L := L) Q'
  letI : ∀ Q', Algebra Vhat (A Q') := fun Q' =>
    completedPrimeValuationSubringCompletionAlgebra
      (V := V) (C := C) (K := K) (L := L) Q'
  letI : Algebra.IsIntegral Vhat (A Q) :=
    completedPrimeValuationSubringCompletionAlgebra_isIntegral
      (V := V) (C := C) (K := K) (L := L) Q
  let hmax := standardDVRToCompletion_maximalIdeal_map_eq V K
  let hres := standardDVRToCompletion_residueFieldMap_bijective V K
  let m := completedGenericTensorChosenIdeal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  letI : m.IsMaximal := completedGenericTensorChosenIdeal_isMaximal
    (R := V) (R' := Vhat) (C := C) (K := K) (L := L) (K' := Khat)
    hmax hres Q.1
  let e := completedGenericTensorChosenComponentFractionRingAlgEquiv
    (V := V) (C := C) (K := K) (L := L) Q
  exact integralClosureEquivOfFractionRingAlgEquiv e

end ChosenTensorComponent

end EtaleFundamentalGroups

end
