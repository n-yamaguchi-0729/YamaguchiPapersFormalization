/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FieldComponent.OfFieldTower
import EtaleFundamentalGroups.Kummer.Normalization.ChosenPrime.Final.BoundaryAwayLocal
import EtaleFundamentalGroups.Kummer.GenericTensor.FieldComponent.BaseEquivRightBijective

/-!
# Primitive boundary Away on the full-field multiplication component

The Tag prime first selects an actual generic component over its pointed
local base.  The pointed fraction-field comparison turns that component into
a literal component of `K ⊗[K] L`; its right coordinate is therefore an
isomorphism, produced without a comparison hypothesis.  We use that
isomorphism to transport the selected normalization prime to `L`.

If the full root field already acts on `L`, multiplication selects a
canonical component of `F' ⊗[K] L`.  Pulling the transported prime back to
this component and then applying the canonical final-tower normalization
comparison produces exactly the `ETag` required by
`etaleChosenLocalFactor_finalComponent_boundaryAway_local`.

No component equality, normalization comparison, or bijectivity statement is
an input to the theorem below.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe uR uC uF uF' uL

/-- The canonical full-field multiplication component contains a
normalization prime at which the primitive Tag boundary Away map is etale.

The only extra field datum is the honest action of `F'` on `L`.  In the
full-root application this action is produced from all target roots before
this theorem is invoked.  The intermediate field `F` is retained so that the
output prime can be transported to the literal second-stage component of the
same tower. -/
theorem
    exists_etaleChosenLocalFactor_fullFieldFinalComponent_boundaryAway_local
    {R : Type uR} {C : Type uC}
    {F : Type uF} {F' : Type uF'} {L : Type uL}
    [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [CommRing C] [IsNoetherianRing C]
    [Algebra R C] [Algebra.Etale R C]
    [Field F] [Field F'] [Field L]
    [Algebra R L]
    [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L]
    [Algebra (FractionRing R) F]
    [Algebra F F'] [Algebra (FractionRing R) F']
    [IsScalarTower (FractionRing R) F F']
    [FiniteDimensional F F']
    [Algebra F' L]
    [IsScalarTower (FractionRing R) F' L]
    (f : R)
    (hAway :
      (Localization.awayMap
        (algebraMap R (integralClosure R L)) f).Etale)
    (P : Ideal C) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R C)
        (P.over_def (IsLocalRing.maximalIdeal R))))
    (e : C ⊗[R] integralClosure R L)
    (P' : Ideal (C ⊗[R] integralClosure R L))
    [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P')
    (hfinite : Module.Finite C (Localization.Away e))
    (hunique : ∀ P'' : Ideal (C ⊗[R] integralClosure R L),
      P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P') :
    let Cₚ := Localization.AtPrime P
    let K := FractionRing R
    let pointed : R ≃ₐ[R] Cₚ :=
      henselianPointedEtaleLocalizationAlgEquiv P hres
    letI : IsDomain Cₚ := pointed.symm.toMulEquiv.isDomain R
    letI : Algebra Cₚ K :=
      pointedBaseReverseFractionRingAlgebra pointed
    let cFullAlgebra : Algebra Cₚ F' :=
      ((algebraMap K F').comp (algebraMap Cₚ K)).toAlgebra
    letI : Algebra Cₚ F' := cFullAlgebra
    let cTargetAlgebra : Algebra Cₚ L :=
      ((algebraMap K L).comp (algebraMap Cₚ K)).toAlgebra
    letI : Algebra Cₚ L := cTargetAlgebra
    let m := fieldTowerTensorComponentIdeal
      (K := K) (K' := F') (L := L)
    letI : m.IsMaximal :=
      fieldTowerTensorComponentIdeal_isMaximal
        (K := K) (K' := F') (L := L)
    let M := GenericTensorFieldComponent m
    letI : Algebra Cₚ M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
    ∃ (p : PrimeSpectrum (integralClosure Cₚ M)),
      let Dfinal := Localization.AtPrime p.asIdeal
      letI : CommRing Dfinal := OreLocalization.instCommRing
      letI : Algebra Cₚ Dfinal := inferInstance
      let fCₚ : Cₚ := algebraMap R Cₚ f
      @Algebra.Etale
        (Localization.Away fCₚ)
        (Localization.Away (algebraMap Cₚ Dfinal fCₚ))
        (OreLocalization.instCommRing (R := Cₚ))
        (OreLocalization.instCommRing (R := Dfinal))
        (Localization.awayMap (algebraMap Cₚ Dfinal) fCₚ).toAlgebra := by
  dsimp only
  let Q := etaleChosenAwayPrime e P'
  let : Q.IsPrime := etaleChosenAwayPrime_isPrime e P' heP'
  let : Q.LiesOver P' :=
    etaleChosenAwayPrime_liesOver e P' heP'
  let : Q.LiesOver P := Ideal.LiesOver.trans Q P' P
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let K := FractionRing R
  let pointed : R ≃ₐ[R] Cₚ :=
    henselianPointedEtaleLocalizationAlgEquiv P hres
  let : IsDomain Cₚ := pointed.symm.toMulEquiv.isDomain R
  let cKAlgebra : Algebra Cₚ K :=
    pointedBaseReverseFractionRingAlgebra pointed
  let : Algebra Cₚ K := cKAlgebra
  let : SMul Cₚ K := cKAlgebra.toSMul
  let cFullAlgebra : Algebra Cₚ F' :=
    ((algebraMap K F').comp (algebraMap Cₚ K)).toAlgebra
  let : Algebra Cₚ F' := cFullAlgebra
  let : SMul Cₚ F' := cFullAlgebra.toSMul
  let cTargetAlgebra : Algebra Cₚ L :=
    ((algebraMap K L).comp (algebraMap Cₚ K)).toAlgebra
  let : Algebra Cₚ L := cTargetAlgebra
  let : SMul Cₚ L := cTargetAlgebra.toSMul
  let : IsScalarTower Cₚ K F' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Cₚ K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Cₚ F' L := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    change algebraMap K L (algebraMap Cₚ K c) =
      algebraMap F' L (algebraMap K F' (algebraMap Cₚ K c))
    exact IsScalarTower.algebraMap_apply K F' L _
  let : Module.Finite R Cₚ :=
    Module.Finite.of_surjective pointed.toLinearMap pointed.surjective
  let : FaithfulSMul R Cₚ :=
    (faithfulSMul_iff_algebraMap_injective R Cₚ).mpr <| by
      intro x y hxy
      apply pointed.injective
      calc
        pointed x = algebraMap R Cₚ x := by
          rw [← pointed.commutes x]
          simp
        _ = algebraMap R Cₚ y := hxy
        _ = pointed y := by
          rw [← pointed.commutes y]
          simp
  obtain ⟨mTag, qTag, ⟨ETagComponent⟩⟩ :=
    exists_etaleChosenLocalFactor_finiteGenericFiberComponent_algEquiv
      (R := R) (C := C) (L := L) P e P' heP'
  obtain ⟨nBase, pBase, ⟨Epointed⟩⟩ :=
    exists_pointedRootRefinedComponent_localizationAlgEquiv
      (R := R) (C := Cₚ) (L := L)
      pointed mTag.asIdeal qTag.asIdeal
  let Mbase := GenericTensorFieldComponent nBase.asIdeal
  let : Algebra Cₚ Mbase :=
    genericTensorFieldComponentLeftScalarAlgebra
      (R := Cₚ) nBase.asIdeal
  let : SMul Cₚ Mbase :=
    (genericTensorFieldComponentLeftScalarAlgebra
      (R := Cₚ) nBase.asIdeal).toSMul
  let : Algebra L Mbase :=
    genericTensorFieldComponentRightAlgebra nBase.asIdeal
  let : IsScalarTower Cₚ K Mbase :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K L Mbase :=
    genericTensorFieldComponent_right_isScalarTower nBase.asIdeal
  let : IsScalarTower Cₚ L Mbase := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [IsScalarTower.algebraMap_apply Cₚ K Mbase,
      IsScalarTower.algebraMap_apply Cₚ K L,
      IsScalarTower.algebraMap_apply K L Mbase]
  have hbase : Function.Bijective (algebraMap K K) := by
    constructor
    · intro x y hxy
      simpa only [Algebra.algebraMap_self_apply] using hxy
    · intro x
      exact ⟨x, Algebra.algebraMap_self_apply x⟩
  have hright : Function.Bijective (algebraMap L Mbase) :=
    genericTensorFieldComponentRight_bijective_of_base_bijective
      (K₀ := K) (K₁ := K) (L := L) hbase nBase.asIdeal
  let eRight : L ≃ₐ[L] Mbase :=
    AlgEquiv.ofBijective (Algebra.ofId L Mbase) hright
  let eBase : Mbase ≃ₐ[Cₚ] L :=
    { toRingEquiv := eRight.symm.toRingEquiv
      commutes' := by
        intro c
        apply eRight.injective
        calc
          eRight (eRight.symm.toRingEquiv.toFun (algebraMap Cₚ Mbase c)) =
              algebraMap Cₚ Mbase c := eRight.apply_symm_apply _
          _ = algebraMap L Mbase (algebraMap Cₚ L c) :=
            IsScalarTower.algebraMap_apply Cₚ L Mbase c
          _ = eRight (algebraMap Cₚ L c) := by
            symm
            simpa only [Algebra.algebraMap_self_apply] using
              eRight.commutes (algebraMap Cₚ L c) }
  let eBaseIC : integralClosure Cₚ Mbase ≃ₐ[Cₚ]
      integralClosure Cₚ L :=
    eBase.mapIntegralClosure
  let pTarget : Ideal (integralClosure Cₚ L) :=
    pBase.asIdeal.map eBaseIC.toRingEquiv
  let : pTarget.IsPrime := by
    apply Ideal.map_isPrime_of_surjective eBaseIC.surjective
    intro x hx
    have hx0 : x = 0 :=
      eBaseIC.injective (hx.trans eBaseIC.map_zero.symm)
    subst x
    exact pBase.asIdeal.zero_mem
  have hpBaseComap :
      pBase.asIdeal = pTarget.comap eBaseIC.toRingHom := by
    symm
    exact Ideal.comap_map_of_bijective
      eBaseIC.toRingEquiv eBaseIC.bijective
  let EbaseLocal : Localization.AtPrime pBase.asIdeal ≃ₐ[Cₚ]
      Localization.AtPrime pTarget :=
    Localization.localAlgEquiv
      pBase.asIdeal pTarget eBaseIC hpBaseComap
  let m := fieldTowerTensorComponentIdeal
    (K := K) (K' := F') (L := L)
  let : m.IsMaximal :=
    fieldTowerTensorComponentIdeal_isMaximal
      (K := K) (K' := F') (L := L)
  let M := GenericTensorFieldComponent m
  let : Algebra Cₚ M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Cₚ) m
  let pFinal := fieldTowerTensorComponentIntegralClosurePrime
    (B := Cₚ) (K := K) (K' := F') (L := L) pTarget
  let : pFinal.IsPrime :=
    fieldTowerTensorComponentIntegralClosurePrime_isPrime
      (B := Cₚ) (K := K) (K' := F') (L := L) pTarget
  let Efield : Localization.AtPrime pFinal ≃ₐ[Cₚ]
      Localization.AtPrime pTarget :=
    fieldTowerTensorComponentIntegralClosureLocalizationAlgEquiv
      (B := Cₚ) (K := K) (K' := F') (L := L) pTarget
  let n := genericTensorTowerIntermediateIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : n.IsMaximal :=
    genericTensorTowerIntermediateIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let q := genericTensorTowerSecondIdeal
    (K := K) (F := F) (F' := F') (L := L) m
  let : q.IsMaximal :=
    genericTensorTowerSecondIdeal_isMaximal
      (K := K) (F := F) (F' := F') (L := L) m
  let pSecond := genericTensorTowerFinalComponentIntegralClosurePrime
    (B := Cₚ) (K := K) (F := F) (F' := F') (L := L)
    m pFinal
  let : pSecond.IsPrime :=
    genericTensorTowerFinalComponentIntegralClosurePrime_isPrime
      (B := Cₚ) (K := K) (F := F) (F' := F') (L := L)
      m pFinal
  let Efinal : Localization.AtPrime pFinal ≃ₐ[Cₚ]
      Localization.AtPrime pSecond :=
    genericTensorTowerFinalComponentIntegralClosureLocalizationAlgEquiv
      (B := Cₚ) (K := K) (F := F) (F' := F') (L := L)
      m pFinal
  let ETag : Dₚ ≃ₐ[Cₚ] Localization.AtPrime pSecond :=
    (((ETagComponent.trans Epointed).trans EbaseLocal).trans
      Efield.symm).trans Efinal
  refine ⟨⟨pFinal, inferInstance⟩, ?_⟩
  exact etaleChosenLocalFactor_finalComponent_boundaryAway_local
    (R := R) (C := C) (S := integralClosure R L)
    (K := K) (F := F) (F' := F') (L := L)
    f hAway P e P' heP' hfinite hunique m pFinal ETag

end EtaleFundamentalGroups.Kummer

end
