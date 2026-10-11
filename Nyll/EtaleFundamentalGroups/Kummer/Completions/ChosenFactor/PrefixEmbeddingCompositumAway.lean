/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.RegularSystem
import Nyll.EtaleFundamentalGroups.Kummer.Completions.GenericTensorTower.ChosenFactorCompositum
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularPair.IntegrallyClosed
import Nyll.EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.Local
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The literal prefix compositum selected by a completed chosen factor

Let `C` be the finite etale residue lift of a complete regular pair and let
`P` be the fraction field of its completed one-root chosen factor.  A
concrete embedding of a finite prefix field `M` into `P` selects an actual
compositum of `M` and `Frac(C)` inside that same `P`.

The theorem below exposes the corresponding literal maximal ideal of
`Frac(C) tensor[Frac(A)] M`.  It also constructs the component embedding
back into `P`, proves both tensor-coordinate formulas, and transports the
original prefix boundary Away statement to the normalization of that
literal component.  No tensor factor, comparison equivalence, or
normalization statement is supplied as an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-! The scalar tower used by the literal component is generated from the
common integral coordinates, rather than requested from its caller. -/

theorem regularPair_fractionFieldTower_of_finiteEtale_commonTarget
    {A C F KC P : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Module.Finite A C] [Algebra.Etale A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field P] [Algebra A P] [Algebra C P]
    [IsScalarTower A C P]
    [Algebra F P] [IsScalarTower A F P]
    [Algebra KC P] [IsScalarTower C KC P]
    (y z : A)
    (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A) :
    IsScalarTower F KC P := by
  let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsDomain C := hgeometryC.2.1
  exact fractionFieldTower_of_common_integral_base
    (A := A) (C := C) (F := F) (KC := KC) (P := P)

/-- A concrete prefix embedding into the fraction field of a completed
chosen factor internally selects its literal finite-residue-lift tensor
component and carries the prefix boundary Away property to that component.

The `C → KC → P` tower and the two common `A`-actions are the root-coordinate
compatibility produced by the completed one-root chosen factor.  The
`F → KC → P` tower is then generated from those integral coordinates.  The
ideal `mKC` is not chosen existentially: it is the pullback of the kernel of
the actual-compositum product map determined by that tower and `fPrefix`. -/
theorem
    completeRegularPair_prefixEmbedding_actualCompositum_boundaryAway
    {A C F KC M P : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Module.Finite A C] [Algebra.Etale A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field M] [Algebra A M] [Algebra F M]
    [IsScalarTower A F M] [FiniteDimensional F M]
    [Algebra.IsSeparable F M]
    [Field P] [Algebra A P] [Algebra C P]
    [IsScalarTower A C P]
    [Algebra F P] [IsScalarTower A F P]
    [Algebra KC P] [IsScalarTower C KC P]
    (y z : A)
    (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (fPrefix : M →ₐ[F] P)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A M)) y).Etale) :
    let hTowerFKCP : IsScalarTower F KC P :=
      regularPair_fractionFieldTower_of_finiteEtale_commonTarget
        (A := A) (C := C) (F := F) (KC := KC) (P := P)
        y z hreg hgen
    letI : IsScalarTower F KC P := hTowerFKCP
    let fKC : KC →ₐ[F] P := IsScalarTower.toAlgHom F KC P
    let Eimage : IntermediateField F P := fPrefix.fieldRange
    let Kimage : IntermediateField F P := fKC.fieldRange
    let hfiniteEimage : FiniteDimensional F Eimage :=
      fPrefix.toLinearMap.finiteDimensional_range
    letI : FiniteDimensional F Eimage := hfiniteEimage
    let eGeneric : (F ⊗[F] M) ≃ₐ[F] Eimage :=
      (Algebra.TensorProduct.lid F M).trans fPrefix.equivFieldRange
    let mActual := actualCompositumGenericComponentIdeal
      (A := F) (T := M) (F := F) (Omega := P)
      Eimage Kimage eGeneric
    let hmActual : mActual.IsMaximal :=
      actualCompositumGenericComponentIdeal_isMaximal
        Eimage Kimage eGeneric
    let eKC : KC ≃ₐ[F] Kimage := fKC.equivFieldRange
    let eTensorKC : (KC ⊗[F] M) ≃ₐ[F] (Kimage ⊗[F] M) :=
      Algebra.TensorProduct.congr eKC (AlgEquiv.refl : M ≃ₐ[F] M)
    let mKC := mActual.comap eTensorKC.toRingEquiv.toRingHom
    let hmKC : mKC.IsMaximal :=
      hmActual.comap_bijective eTensorKC.toRingEquiv.toRingHom
        eTensorKC.bijective
    letI : mKC.IsMaximal := hmKC
    let Omega := GenericTensorFieldComponent mKC
    letI : Algebra C Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := C) mKC
    ∃ omegaToP : Omega →ₐ[KC] P,
      Function.Injective omegaToP ∧
        (∀ x : KC,
          omegaToP (genericTensorFieldComponentLeft mKC x) =
            algebraMap KC P x) ∧
        (∀ c : C,
          omegaToP
              (genericTensorFieldComponentLeft mKC
                (algebraMap C KC c)) =
            algebraMap C P c) ∧
        (∀ x : M,
          omegaToP (genericTensorFieldComponentRight mKC x) =
            fPrefix x) ∧
        letI : Algebra Omega P := omegaToP.toRingHom.toAlgebra
        IsScalarTower KC Omega P ∧
          (Localization.awayMap
            (algebraMap C (integralClosure C Omega))
            (algebraMap A C y)).Etale := by
  classical
  dsimp only
  let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
  let : IsRegularLocalRing A :=
    isRegularLocalRing_of_regularSystem [y, z] hreg hgen
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsNoetherianRing C := hgeometryC.1
  let : IsDomain C := hgeometryC.2.1
  let yC := algebraMap A C y
  let zC := algebraMap A C z
  have hregC : RingTheory.Sequence.IsRegular C [yC, zC] := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.1
  have hgenC : Ideal.ofList [yC, zC] = IsLocalRing.maximalIdeal C := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.2.1
  let : IsIntegrallyClosed C :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
      C yC zC hregC hgenC
  let : IsScalarTower F KC P :=
    regularPair_fractionFieldTower_of_finiteEtale_commonTarget
      (A := A) (C := C) (F := F) (KC := KC) (P := P)
      y z hreg hgen
  let fKC : KC →ₐ[F] P := IsScalarTower.toAlgHom F KC P
  let Eimage : IntermediateField F P := fPrefix.fieldRange
  let Kimage : IntermediateField F P := fKC.fieldRange
  let : FiniteDimensional F Eimage :=
    fPrefix.toLinearMap.finiteDimensional_range
  let eGeneric : (F ⊗[F] M) ≃ₐ[F] Eimage :=
    (Algebra.TensorProduct.lid F M).trans fPrefix.equivFieldRange
  let mActual := actualCompositumGenericComponentIdeal
    (A := F) (T := M) (F := F) (Omega := P)
    Eimage Kimage eGeneric
  let : mActual.IsMaximal :=
    actualCompositumGenericComponentIdeal_isMaximal
      Eimage Kimage eGeneric
  let eKC : KC ≃ₐ[F] Kimage := fKC.equivFieldRange
  let eTensorKC : (KC ⊗[F] M) ≃ₐ[F] (Kimage ⊗[F] M) :=
    Algebra.TensorProduct.congr eKC (AlgEquiv.refl : M ≃ₐ[F] M)
  let mKC := mActual.comap eTensorKC.toRingEquiv.toRingHom
  let : mKC.IsMaximal :=
    (inferInstance : mActual.IsMaximal).comap_bijective
      eTensorKC.toRingEquiv.toRingHom eTensorKC.bijective
  let Omega := GenericTensorFieldComponent mKC
  let : Algebra C Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := C) mKC
  let C₀ := integralClosure A M
  let : Module.Finite A C₀ :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := F) hdim
  let : IsFractionRing C₀ M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F M C₀
  let : FaithfulSMul A C₀ :=
    (faithfulSMul_iff_algebraMap_injective A C₀).mpr fun x w hxw ↦ by
      apply (IsFractionRing.injective A F)
      apply (algebraMap F M).injective
      have hxM := congrArg (fun c : C₀ ↦ (c : M)) hxw
      change algebraMap A M x = algebraMap A M w at hxM
      calc
        algebraMap F M (algebraMap A F x) = algebraMap A M x :=
          (IsScalarTower.algebraMap_apply A F M x).symm
        _ = algebraMap A M w := hxM
        _ = algebraMap F M (algebraMap A F w) :=
          IsScalarTower.algebraMap_apply A F M w
  have hyne : y ≠ 0 :=
    (prime_of_mem_regularSystem hreg hgen (by simp)).ne_zero
  have hAwayOmega :
      (Localization.awayMap
        (algebraMap C (integralClosure C Omega)) yC).Etale := by
    simpa only [yC, C₀, Omega] using
      (localization_away_integralClosure_genericTensorFieldComponent_etale_of_awayMap
        (A := A) (C := C₀) (D := C)
        (F := F) (E := M) (K := KC)
        y hyne hAway mKC)
  have hmMap :
      mActual = mKC.map eTensorKC.toRingEquiv.toRingHom := by
    exact (Ideal.map_comap_of_surjective
      eTensorKC.toRingEquiv.toRingHom eTensorKC.surjective mActual).symm
  let eComponent : Omega ≃ₐ[F]
      GenericTensorFieldComponent mActual :=
    Ideal.quotientEquivAlg mKC mActual eTensorKC hmMap
  let eActualF : GenericTensorFieldComponent mActual ≃ₐ[F]
      (Eimage ⊔ Kimage : IntermediateField F P) :=
    (actualCompositumGenericComponentAlgEquiv
      Eimage Kimage eGeneric).restrictScalars F
  let eAmbientF : Omega ≃ₐ[F]
      (Eimage ⊔ Kimage : IntermediateField F P) :=
    eComponent.trans eActualF
  let ambientInclusion :
      (Eimage ⊔ Kimage : IntermediateField F P) →ₐ[F] P :=
    (Eimage ⊔ Kimage : IntermediateField F P).val
  let omegaToPF : Omega →ₐ[F] P :=
    ambientInclusion.comp eAmbientF.toAlgHom
  let omegaToP : Omega →ₐ[KC] P :=
    { omegaToPF.toRingHom with
      commutes' := by
        intro x
        change omegaToPF (genericTensorFieldComponentLeft mKC x) =
          algebraMap KC P x
        change
          (((actualCompositumGenericComponentAlgEquiv
              Eimage Kimage eGeneric)
            (Ideal.quotientEquivAlg mKC mActual eTensorKC hmMap
              (genericTensorFieldComponentLeft mKC x)) :
                (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
            algebraMap KC P x
        rw [genericTensorFieldComponentLeft_apply,
          Ideal.quotientEquivAlg_mk mActual eTensorKC hmMap,
          actualCompositumGenericComponentAlgEquiv_mk]
        change
          (((actualCompositumGenericComponentMap Eimage Kimage eGeneric)
            (eTensorKC
              ((Algebra.TensorProduct.includeLeft :
                KC →ₐ[F] KC ⊗[F] M) x)) :
              (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
            algebraMap KC P x
        rw [show eTensorKC
            ((Algebra.TensorProduct.includeLeft :
              KC →ₐ[F] KC ⊗[F] M) x) =
              (Algebra.TensorProduct.includeLeft :
                Kimage →ₐ[F] Kimage ⊗[F] M) (eKC x) by
          change eTensorKC (x ⊗ₜ[F] (1 : M)) =
            eKC x ⊗ₜ[F] (1 : M)
          simp [eTensorKC]]
        change
          (((actualCompositumGenericComponentMap Eimage Kimage eGeneric)
              ((eKC x) ⊗ₜ[F] (1 : M)) :
                (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
            algebraMap KC P x
        rw [actualCompositumGenericComponentMap_tmul_left_coe]
        rfl }
  have hLeftCoordinate (x : KC) :
      omegaToP (genericTensorFieldComponentLeft mKC x) =
        algebraMap KC P x :=
    omegaToP.commutes x
  have hBaseCoordinate (c : C) :
      omegaToP
          (genericTensorFieldComponentLeft mKC
            (algebraMap C KC c)) =
        algebraMap C P c := by
    rw [hLeftCoordinate]
    exact (IsScalarTower.algebraMap_apply C KC P c).symm
  have hRightCoordinate (x : M) :
      omegaToP (genericTensorFieldComponentRight mKC x) =
        fPrefix x := by
    change
      (((actualCompositumGenericComponentAlgEquiv
            Eimage Kimage eGeneric)
          (Ideal.quotientEquivAlg mKC mActual eTensorKC hmMap
            (genericTensorFieldComponentRight mKC x)) :
              (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
        fPrefix x
    rw [genericTensorFieldComponentRight_apply,
      Ideal.quotientEquivAlg_mk mActual eTensorKC hmMap,
      actualCompositumGenericComponentAlgEquiv_mk]
    change
      (((actualCompositumGenericComponentMap Eimage Kimage eGeneric)
          (eTensorKC
            ((Algebra.TensorProduct.includeRight :
              M →ₐ[F] KC ⊗[F] M) x)) :
            (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
        fPrefix x
    rw [show eTensorKC
        ((Algebra.TensorProduct.includeRight :
          M →ₐ[F] KC ⊗[F] M) x) =
          (Algebra.TensorProduct.includeRight :
            M →ₐ[F] Kimage ⊗[F] M) x by
      change eTensorKC ((1 : KC) ⊗ₜ[F] x) =
        (1 : Kimage) ⊗ₜ[F] x
      simp [eTensorKC]]
    change
      (((actualCompositumGenericComponentMap Eimage Kimage eGeneric)
          ((1 : Kimage) ⊗ₜ[F] x) :
            (Eimage ⊔ Kimage : IntermediateField F P)) : P) =
        fPrefix x
    rw [actualCompositumGenericComponentMap_tmul_right_coe]
    simpa only [eGeneric, AlgEquiv.trans_apply, Algebra.TensorProduct.lid_tmul, one_smul]
      using AlgHom.equivFieldRange_apply_coe (f := fPrefix) x
  let : Algebra Omega P := omegaToP.toRingHom.toAlgebra
  have hTowerOmega : IsScalarTower KC Omega P := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    exact (omegaToP.commutes x).symm
  exact ⟨omegaToP, omegaToP.injective, hLeftCoordinate,
    hBaseCoordinate, hRightCoordinate, hTowerOmega, hAwayOmega⟩

end EtaleFundamentalGroups.Kummer

end
