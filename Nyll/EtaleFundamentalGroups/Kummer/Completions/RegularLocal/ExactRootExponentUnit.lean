/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Away.AlgEquivTransport
import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BoundaryAwayFieldEquiv
import Nyll.EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExponentUnit.Core
import Nyll.EtaleFundamentalGroups.Kummer.Completions.RegularLocal.ExactRootRightComparison
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.RegularSystem
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularPair.IntegrallyClosed

/-!
# The maximal-adic chosen-factor terminal for one selected root

Work over a complete two-dimensional regular local prefix `A`, with selected
parameter `y`.  The actual finite-etale local factor `D` of the one-root
cover becomes the literal root cover after the explicit finite residue lift
`C / A`.

If a prefix component over `Frac(C)` has the exact selected height-one
ramification index, the complete regular-local degree sandwich identifies it
with `Frac(D)`.  Mapping integral closures along this sourced field
equivalence identifies the prefix normalization with `D`; regular-system
geometry proves internally that the root factor is integrally closed.  The
prefix boundary Away property therefore transports to `D`.  Composing with
the finite-etale base `A -> C` gives the literal boundary Away map required by
the complete chosen-factor exponent terminal.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open RingTheory.Sequence
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

private theorem
    finiteEtaleResidueLift_pair_adjoinRoot_isDomain_exponentUnit
    {A l : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    {N : ℕ} (hN : 0 < N) :
    let C := FiniteEtaleResidueLift A l
    letI : IsDomain C :=
      finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
    IsDomain
      (AdjoinRoot (X ^ N - Polynomial.C (algebraMap A C y))) := by
  dsimp only
  let C := FiniteEtaleResidueLift A l
  let yC := algebraMap A C y
  let zC := algebraMap A C z
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  have hgeometry :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  have hregC : IsRegular C [yC, zC] := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometry.2.2.1
  have hgenC : Ideal.ofList [yC, zC] = IsLocalRing.maximalIdeal C := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometry.2.2.2.1
  have hymax : yC ∈ IsLocalRing.maximalIdeal C := by
    rw [← hgenC]
    exact Ideal.subset_span (by simp)
  let : IsLocalRing (AdjoinRoot (X ^ N - Polynomial.C yC)) :=
    isLocalRing_adjoinRoot_X_pow_sub_C hN hymax
  exact
    (localRootCover_regularSystem_geometry
      (R := C) (a := yC) (rs := [zC]) hN hregC hgenC).2.1

private theorem fractionRingTargetBase_toSMul_faithful_exponentUnit
    {C R D : Type u}
    [CommRing C] [IsDomain C]
    [CommRing R] [IsDomain R] [Algebra C R] [FaithfulSMul C R]
    [CommRing D] [IsDomain D] [Algebra C D]
    (e : R ≃ₐ[C] D) :
    @FaithfulSMul C (FractionRing D)
      (fractionRingTargetBaseAlgebraOfAlgEquiv e).toSMul := by
  apply (@faithfulSMul_iff_algebraMap_injective
    C (FractionRing D) _ _
      (fractionRingTargetBaseAlgebraOfAlgEquiv e)).mpr
  have hCD : Function.Injective (algebraMap C D) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective C R
    apply e.injective
    simpa only [e.commutes] using hxy
  change Function.Injective
    ((algebraMap D (FractionRing D)).comp (algebraMap C D))
  exact (IsFractionRing.injective D (FractionRing D)).comp hCD

private theorem fractionRingTargetBase_toSMul_isScalarTower_exponentUnit
    {C R D : Type u}
    [CommRing C] [CommRing R] [CommRing D]
    [Algebra C R] [Algebra C D] [IsDomain D]
    (e : R ≃ₐ[C] D) :
    @IsScalarTower C D (FractionRing D)
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D (FractionRing D)).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv e).toSMul := by
  refine @IsScalarTower.of_algebraMap_eq C D (FractionRing D)
    _ _ _ (inferInstance : Algebra C D)
      (inferInstance : Algebra D (FractionRing D))
      (fractionRingTargetBaseAlgebraOfAlgEquiv e) ?_
  intro x
  rfl

private theorem fractionRingAlgebra_toSMul_isScalarTower_exponentUnit
    {C R D : Type u}
    [CommRing C] [IsDomain C]
    [CommRing R] [IsDomain R] [Algebra C R] [FaithfulSMul C R]
    [CommRing D] [IsDomain D] [Algebra C D]
    (e : R ≃ₐ[C] D) :
    @IsScalarTower C (FractionRing C) (FractionRing D)
      (inferInstance : Algebra C (FractionRing C)).toSMul
      (fractionRingAlgebraOfAlgEquiv e).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv e).toSMul := by
  let : Algebra C (FractionRing D) :=
    fractionRingTargetBaseAlgebraOfAlgEquiv e
  let : @FaithfulSMul C (FractionRing D)
      (fractionRingTargetBaseAlgebraOfAlgEquiv e).toSMul :=
    fractionRingTargetBase_toSMul_faithful_exponentUnit e
  let : Algebra (FractionRing C) (FractionRing D) :=
    fractionRingAlgebraOfAlgEquiv e
  exact FractionRing.isScalarTower_liftAlgebra C (FractionRing D)

private theorem compositeAlgebra_toSMul_isScalarTower_exponentUnit
    {C K E : Type u}
    [CommRing C] [CommRing K] [CommRing E]
    [Algebra C K] [Algebra K E] :
    @IsScalarTower C K E
      (inferInstance : Algebra C K).toSMul
      (inferInstance : Algebra K E).toSMul
      (((algebraMap K E).comp (algebraMap C K)).toAlgebra).toSMul := by
  refine @IsScalarTower.of_algebraMap_eq C K E
    _ _ _ (inferInstance : Algebra C K)
      (inferInstance : Algebra K E)
      ((algebraMap K E).comp (algebraMap C K)).toAlgebra ?_
  intro x
  rfl

/-- If `C / A` is etale and the localized map `C_y -> D_y` is etale, then
the literal localized composite `A_y -> D_y` is etale.

Unlike `localization_awayMap_etale_of_etale_extension`, the etale map here is
on the base side of the tower.  The proof identifies `C_y` with the scalar
extension of `C` to `A_y`, then composes the two localized maps. -/
theorem localization_awayMap_etale_of_etale_base_and_away_extension
    {A C D : Type*}
    [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra C D] [Algebra.Etale A C]
    (f : A)
    (hAway :
      (Localization.awayMap (algebraMap C D) (algebraMap A C f)).Etale) :
    (Localization.awayMap
      ((algebraMap C D).comp (algebraMap A C)) f).Etale := by
  let fC : C := algebraMap A C f
  let fD : D := algebraMap C D fC
  let S := Localization.Away f
  let T := Localization.Away fC
  let U := Localization.Away fD
  let mapST : S →+* T :=
    Localization.awayMap (algebraMap A C) f
  let mapTU : T →+* U :=
    Localization.awayMap (algebraMap C D) fC
  let mapSU : S →+* U :=
    Localization.awayMap
      ((algebraMap C D).comp (algebraMap A C)) f
  let : Algebra S T := mapST.toAlgebra
  let : Algebra T U := mapTU.toAlgebra
  let : Algebra S U := mapSU.toAlgebra
  have hcomp : mapTU.comp mapST = mapSU := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext a
    simp only [RingHom.comp_apply]
    calc
      mapTU (mapST (algebraMap A S a)) =
          mapTU (algebraMap C T (algebraMap A C a)) := by
        rw [show mapST (algebraMap A S a) =
            algebraMap C T (algebraMap A C a) by
          change IsLocalization.map T (algebraMap A C) _
              (algebraMap A S a) = algebraMap C T (algebraMap A C a)
          exact IsLocalization.map_eq _ a]
      _ = algebraMap D U (algebraMap C D (algebraMap A C a)) := by
        change IsLocalization.map U (algebraMap C D) _
            (algebraMap C T (algebraMap A C a)) = _
        exact IsLocalization.map_eq _ (algebraMap A C a)
      _ = mapSU (algebraMap A S a) := by
        change algebraMap D U
            (((algebraMap C D).comp (algebraMap A C)) a) =
          IsLocalization.map U
            ((algebraMap C D).comp (algebraMap A C)) _
              (algebraMap A S a)
        exact (IsLocalization.map_eq _ a).symm
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (DFunLike.congr_fun hcomp x).symm
  have hST : Algebra.Etale S T := by
    let : IsScalarTower A C T := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A S T := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      change algebraMap A T a = mapST (algebraMap A S a)
      rw [IsScalarTower.algebraMap_apply A C T]
      simp [mapST, S, T, fC, IsLocalization.Away.map]
    let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway f
    let : Algebra.Etale C T := Algebra.Etale.of_isLocalizationAway fC
    let : Algebra.Etale A T := Algebra.Etale.comp A C T
    exact Algebra.Etale.of_restrictScalars A S T
  let : Algebra.Etale S T := hST
  let : Algebra.Etale T U := by
    simpa only [mapTU, fC, fD, T, U] using hAway.toAlgebra
  exact (show Algebra.Etale S U from Algebra.Etale.comp S T U)

/-- Source terminal for a completed one-root chosen factor over a regular
parameter pair.

The returned tensor coordinate is the actual complete chosen-factor
coordinate.  In its dependent continuation, `Omega` is the literal
finite-residue-base-changed prefix component.  The selected-height-one DVR
comparison and its exact ramification equality are the concrete outputs of
etale tensor base change.  From them and the prefix normalization Away
property this theorem produces `N` as a unit in the original complete local
ring.

No field degree, right-coordinate bijectivity, normalization comparison, or
boundary Away statement for `D` is a public input. -/
theorem
    exists_completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_prefixNormalizationAway
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A))) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    letI : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            letI : IsDomain Rn :=
              finiteEtaleResidueLift_pair_adjoinRoot_isDomain_exponentUnit
                y z hreg hgen hN
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            letI : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_faithful_exponentUnit eRoot
            letI : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_isScalarTower_exponentUnit eRoot
            letI : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            letI : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebra_toSMul_isScalarTower_exponentUnit eRoot
            ∀ {Omega : Type u} [Field Omega]
              [Algebra KC Omega] [Algebra Omega P]
              [IsScalarTower KC Omega P],
              ∀ (base : DVF.{u, v} KC) (target : DVF.{u, w} Omega)
                [base.valuation.HasExtension target.valuation]
                [Module.Finite base.valuationSubring
                  target.valuationSubring],
                ramificationIndex base target = N →
                  letI : Algebra C Omega :=
                    ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
                  letI : @IsScalarTower C KC Omega
                      (inferInstance : Algebra C KC).toSMul
                      (inferInstance : Algebra KC Omega).toSMul
                      (((algebraMap KC Omega).comp
                        (algebraMap C KC)).toAlgebra).toSMul :=
                    compositeAlgebra_toSMul_isScalarTower_exponentUnit
                  letI : @IsScalarTower C Omega P
                      (((algebraMap KC Omega).comp
                        (algebraMap C KC)).toAlgebra).toSMul
                      (inferInstance : Algebra Omega P).toSMul
                      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
                    IsScalarTower.of_algebraMap_eq fun x ↦ by
                      change algebraMap C P x = algebraMap Omega P
                        (algebraMap KC Omega (algebraMap C KC x))
                      calc
                        algebraMap C P x =
                            algebraMap KC P (algebraMap C KC x) :=
                          IsScalarTower.algebraMap_apply C KC P x
                        _ = algebraMap Omega P
                            (algebraMap KC Omega (algebraMap C KC x)) :=
                          IsScalarTower.algebraMap_apply KC Omega P _
                  (Localization.awayMap
                    (algebraMap C (integralClosure C Omega)) yC).Etale →
                    IsUnit (N : A) := by
  intro n a B hymax D _ _ _ _ _ _ q _ _ hunique k kB l eResidue C
  let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
  have hn : ∀ i, 0 < n i := fun _ ↦ hN
  have ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := fun _ ↦ hymax
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) (fun _ ↦ hymax)
  let : Module.Finite A B := finite_iteratedRadical n a (fun _ ↦ hN)
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  let : IsLocalRing D := isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB := AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  have hChosenComparison :=
    exists_completeRegularLocalChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactRamification
      hreg hgen N hN y (by exact List.mem_cons_self) (D := D) q hunique
  let eTensor : (B ⊗[A] C) ≃ₐ[B] D := Classical.choose hChosenComparison
  refine ⟨eTensor, ?_⟩
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  let : IsScalarTower A C D :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      calc
        algebraMap A D x = algebraMap B D (algebraMap A B x) :=
          IsScalarTower.algebraMap_apply A B D x
        _ = eTensor (algebraMap B (B ⊗[A] C) (algebraMap A B x)) :=
          (eTensor.commutes (algebraMap A B x)).symm
        _ = eTensor
            (Algebra.TensorProduct.includeRight (algebraMap A C x)) := by
          congr 1
          exact DFunLike.congr_fun
            Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x
        _ = algebraMap C D (algebraMap A C x) := rfl
  intro yC Rn eRoot P KC
  let zC := algebraMap A C z
  let : IsDomain Rn :=
    finiteEtaleResidueLift_pair_adjoinRoot_isDomain_exponentUnit
      y z hreg hgen hN
  let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C Rn :=
    (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
  let : FaithfulSMul C Rn := inferInstance
  let : Algebra C P := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C P
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBase_toSMul_faithful_exponentUnit eRoot
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBase_toSMul_isScalarTower_exponentUnit eRoot
  let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
  let : @IsScalarTower C KC P
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingAlgebra_toSMul_isScalarTower_exponentUnit eRoot
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsNoetherianRing C := hgeometryC.1
  have hregC : IsRegular C [yC, zC] := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.1
  have hgenC : Ideal.ofList [yC, zC] = IsLocalRing.maximalIdeal C := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.2.1
  have hyCmax : yC ∈ IsLocalRing.maximalIdeal C := by
    rw [← hgenC]
    exact Ideal.subset_span (by exact List.mem_cons_self)
  let : IsLocalRing Rn := by
    simpa only [Rn] using
      isLocalRing_adjoinRoot_X_pow_sub_C hN hyCmax
  have hgeometryRn :=
    localRootCover_regularSystem_geometry
      (R := C) (a := yC) (rs := [zC]) hN hregC hgenC
  let : IsNoetherianRing Rn := by
    simpa only [Rn] using hgeometryRn.1
  have hregRn : IsRegular Rn
      [AdjoinRoot.root (X ^ N - Polynomial.C yC), algebraMap C Rn zC] := by
    simpa only [Rn, localRootCoverParameterList,
      List.map_cons, List.map_nil, AdjoinRoot.algebraMap_eq] using
        hgeometryRn.2.2.1
  have hgenRn : Ideal.ofList
      [AdjoinRoot.root (X ^ N - Polynomial.C yC), algebraMap C Rn zC] =
        IsLocalRing.maximalIdeal Rn := by
    simpa only [Rn, localRootCoverParameterList,
      List.map_cons, List.map_nil, AdjoinRoot.algebraMap_eq] using
        hgeometryRn.2.2.2.1
  let : IsIntegrallyClosed Rn :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
      Rn (AdjoinRoot.root (X ^ N - Polynomial.C yC))
        (algebraMap C Rn zC) hregRn hgenRn
  let : IsIntegrallyClosed D := IsIntegrallyClosed.of_equiv eRoot.toRingEquiv
  let : Module.Finite C Rn :=
    (monic_X_pow_sub_C yC hN.ne').finite_adjoinRoot
  let : Module.Finite C D := Module.Finite.equiv eRoot.toLinearEquiv
  let : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  let : IsIntegralClosure D C P :=
    IsIntegralClosure.of_isIntegrallyClosed D C P
  intro Omega _ _ _ _ base target _ _ hExact
  let : Algebra C Omega :=
    ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
  let : @IsScalarTower C KC Omega
      (inferInstance : Algebra C KC).toSMul
      (inferInstance : Algebra KC Omega).toSMul
      (((algebraMap KC Omega).comp
        (algebraMap C KC)).toAlgebra).toSMul :=
    compositeAlgebra_toSMul_isScalarTower_exponentUnit
  let : @IsScalarTower C Omega P
      (((algebraMap KC Omega).comp
        (algebraMap C KC)).toAlgebra).toSMul
      (inferInstance : Algebra Omega P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap C P x = algebraMap Omega P
        (algebraMap KC Omega (algebraMap C KC x))
      calc
        algebraMap C P x = algebraMap KC P (algebraMap C KC x) :=
          IsScalarTower.algebraMap_apply C KC P x
        _ = algebraMap Omega P
            (algebraMap KC Omega (algebraMap C KC x)) :=
          IsScalarTower.algebraMap_apply KC Omega P _
  intro hAwayOmega
  have hbij : Function.Bijective (algebraMap Omega P) :=
    Classical.choose_spec hChosenComparison base target hExact
  have hAwayP : RingHom.Etale
      (R := Localization.Away yC)
      (S := Localization.Away
        (algebraMap C (integralClosure C P) yC))
      (Localization.awayMap
        (algebraMap C (integralClosure C P)) yC) := by
    exact integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := C) (L := Omega) (P := P) hbij yC hAwayOmega
  let chosenEquiv : integralClosure C P ≃ₐ[C] D :=
    IsIntegralClosure.equiv C (integralClosure C P) P D
  have hAwayCD :
      (Localization.awayMap (algebraMap C D) yC).Etale :=
    localization_awayMap_etale_of_algEquiv chosenEquiv yC hAwayP
  have hAwayComposite :=
    localization_awayMap_etale_of_etale_base_and_away_extension
      (A := A) (C := C) (D := D) y hAwayCD
  have hAwayAD :
      (Localization.awayMap (algebraMap A D) y).Etale := by
    have hMap : algebraMap A D =
        (algebraMap C D).comp (algebraMap A C) :=
      IsScalarTower.algebraMap_eq A C D
    rw [hMap]
    exact hAwayComposite
  have hyPrime : Prime y :=
    prime_of_mem_regularSystem hreg hgen (by exact List.mem_cons_self)
  have hAwayProduct :
      (Localization.awayMap (algebraMap A D) (∏ i, a i)).Etale := by
    rw [Fin.prod_univ_one a]
    exact hAwayAD
  have hUnit :=
    all_exponents_isUnit_of_completeChosenFactor
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      n a hn ha (fun _ ↦ hyPrime) (fun _ ↦ hCharZero)
      (D := D) q hunique hAwayProduct (0 : Fin 1)
  simpa only [n] using hUnit

private theorem
    completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_exactNormalizationPrime
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A))) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (by exact List.mem_cons_self)
    let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
    let : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          let : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          let : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          let : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          let : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          let : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          let : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          let : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          let : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          let : Module.Finite k l := Module.Finite.trans kB l
          let : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          let : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          let : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            let : IsDomain Rn :=
              finiteEtaleResidueLift_pair_adjoinRoot_isDomain_exponentUnit
                y z hreg hgen hN
            let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            let : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            let : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            let : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            let : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_faithful_exponentUnit eRoot
            let : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_isScalarTower_exponentUnit eRoot
            let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            let : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebra_toSMul_isScalarTower_exponentUnit eRoot
            ∀ {K₀ L₀ : Type u} [Field K₀] [Field L₀]
              [Algebra K₀ KC] [Algebra K₀ L₀]
              [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀],
              ∀ (m : Ideal (KC ⊗[K₀] L₀)) (hm : m.IsMaximal),
                let : m.IsMaximal := hm
                let Omega := GenericTensorFieldComponent m
                let : Algebra C Omega :=
                  ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
                let : @IsScalarTower C KC Omega
                    (inferInstance : Algebra C KC).toSMul
                    (inferInstance : Algebra KC Omega).toSMul
                    (((algebraMap KC Omega).comp
                      (algebraMap C KC)).toAlgebra).toSMul :=
                  compositeAlgebra_toSMul_isScalarTower_exponentUnit
                ∀ [Algebra Omega P] [IsScalarTower KC Omega P],
                  let pC := Ideal.span ({yC} : Set C)
                  ∀ (Q : Ideal (integralClosure C Omega)) [Q.IsPrime]
                    [Q.LiesOver pC],
                    Q.ramificationIdx C = N →
                      (Localization.awayMap
                        (algebraMap C (integralClosure C Omega)) yC).Etale →
                        IsUnit (N : A) := by
  intro n a B hymax domainA localB D _ _ _ _ _ _ q _ _ hunique
    finiteAB ffAB integralAB localHomAB completeB localD localHomBD ffBD localHomAD
    k kB l eResidue finitekkB finitekl separablekkB separablekl C domainC
  have hn : ∀ i, 0 < n i := fun _ ↦ hN
  have ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := fun _ ↦ hymax
  obtain ⟨eTensor, hCompare⟩ :=
    (
exists_completeRegularLocalChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactNormalizationPrime
      y z hreg hgen N hN hCharZero (D := D) q hunique)
  refine ⟨eTensor, ?_⟩
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  intro algCD
  let : IsScalarTower A C D :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      calc
        algebraMap A D x = algebraMap B D (algebraMap A B x) :=
          IsScalarTower.algebraMap_apply A B D x
        _ = eTensor (algebraMap B (B ⊗[A] C) (algebraMap A B x)) :=
          (eTensor.commutes (algebraMap A B x)).symm
        _ = eTensor
            (Algebra.TensorProduct.includeRight (algebraMap A C x)) := by
          congr 1
          exact DFunLike.congr_fun
            Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x
        _ = algebraMap C D (algebraMap A C x) := rfl
  intro yC Rn eRoot domainRn domainD freeCRn faithfulCRn P KC
    algCP faithfulCP towerCDP algKCP towerCKCP
  let zC := algebraMap A C z
  have hgeometryC :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C) (ps := [y, z]) hreg hgen
  let : IsNoetherianRing C := hgeometryC.1
  have hregC : IsRegular C [yC, zC] := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.1
  have hgenC : Ideal.ofList [yC, zC] = IsLocalRing.maximalIdeal C := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometryC.2.2.2.1
  have hyCmax : yC ∈ IsLocalRing.maximalIdeal C := by
    rw [← hgenC]
    exact Ideal.subset_span (by exact List.mem_cons_self)
  let : IsLocalRing Rn := by
    simpa only [Rn] using
      isLocalRing_adjoinRoot_X_pow_sub_C hN hyCmax
  have hgeometryRn :=
    localRootCover_regularSystem_geometry
      (R := C) (a := yC) (rs := [zC]) hN hregC hgenC
  let : IsNoetherianRing Rn := by
    simpa only [Rn] using hgeometryRn.1
  have hregRn : IsRegular Rn
      [AdjoinRoot.root (X ^ N - Polynomial.C yC), algebraMap C Rn zC] := by
    simpa only [Rn, localRootCoverParameterList,
      List.map_cons, List.map_nil, AdjoinRoot.algebraMap_eq] using
        hgeometryRn.2.2.1
  have hgenRn : Ideal.ofList
      [AdjoinRoot.root (X ^ N - Polynomial.C yC), algebraMap C Rn zC] =
        IsLocalRing.maximalIdeal Rn := by
    simpa only [Rn, localRootCoverParameterList,
      List.map_cons, List.map_nil, AdjoinRoot.algebraMap_eq] using
        hgeometryRn.2.2.2.1
  let : IsIntegrallyClosed Rn :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegular_pair_of_span_eq_maximalIdeal
      Rn (AdjoinRoot.root (X ^ N - Polynomial.C yC))
        (algebraMap C Rn zC) hregRn hgenRn
  let : IsIntegrallyClosed D := IsIntegrallyClosed.of_equiv eRoot.toRingEquiv
  let : Module.Finite C Rn :=
    (monic_X_pow_sub_C yC hN.ne').finite_adjoinRoot
  let : Module.Finite C D := Module.Finite.equiv eRoot.toLinearEquiv
  let : Algebra.IsIntegral C D := Algebra.IsIntegral.of_finite C D
  let : IsIntegralClosure D C P :=
    IsIntegralClosure.of_isIntegrallyClosed D C P
  intro K₀ L₀ _ _ _ _ _ _ m hm hmCached Omega algCOmega towerCKCOmega
    _ _ pC Q _ _ hExact hAwayOmega
  let : @IsScalarTower C Omega P
      (((algebraMap KC Omega).comp
        (algebraMap C KC)).toAlgebra).toSMul
      (inferInstance : Algebra Omega P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap C P x = algebraMap Omega P
        (algebraMap KC Omega (algebraMap C KC x))
      calc
        algebraMap C P x = algebraMap KC P (algebraMap C KC x) :=
          IsScalarTower.algebraMap_apply C KC P x
        _ = algebraMap Omega P
            (algebraMap KC Omega (algebraMap C KC x)) :=
          IsScalarTower.algebraMap_apply KC Omega P _
  have hbij : Function.Bijective (algebraMap Omega P) :=
    hCompare (K₀ := K₀) (L₀ := L₀) m hm Q hExact
  have hAwayP : RingHom.Etale
      (R := Localization.Away yC)
      (S := Localization.Away
        (algebraMap C (integralClosure C P) yC))
      (Localization.awayMap
        (algebraMap C (integralClosure C P)) yC) := by
    exact integralClosure_boundaryAway_of_bijective_fieldTower_algebraMap
      (A := C) (L := Omega) (P := P) hbij yC hAwayOmega
  let chosenEquiv : integralClosure C P ≃ₐ[C] D :=
    IsIntegralClosure.equiv C (integralClosure C P) P D
  have hAwayCD :
      (Localization.awayMap (algebraMap C D) yC).Etale :=
    localization_awayMap_etale_of_algEquiv chosenEquiv yC hAwayP
  have hAwayComposite :=
    localization_awayMap_etale_of_etale_base_and_away_extension
      (A := A) (C := C) (D := D) y hAwayCD
  have hAwayAD :
      (Localization.awayMap (algebraMap A D) y).Etale := by
    have hMap : algebraMap A D =
        (algebraMap C D).comp (algebraMap A C) :=
      IsScalarTower.algebraMap_eq A C D
    rw [hMap]
    exact hAwayComposite
  have hyPrime : Prime y :=
    prime_of_mem_regularSystem hreg hgen (by exact List.mem_cons_self)
  have hAwayProduct :
      (Localization.awayMap (algebraMap A D) (∏ i, a i)).Etale := by
    rw [Fin.prod_univ_one a]
    exact hAwayAD
  have hUnit :=
    all_exponents_isUnit_of_completeChosenFactor
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
      n a hn ha (fun _ ↦ hyPrime) (fun _ ↦ hCharZero)
      (D := D) q hunique hAwayProduct (0 : Fin 1)
  simpa only [n] using hUnit

/-- Source terminal whose exact selected-height-one input is a prime of the
normalization of a literal Galois tensor component.

Compared with
`exists_completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_prefixNormalizationAway`,
this version exposes no valued field and no finite valuation-subring
extension.  The Galois component makes its ramification index divide its
field degree, and the complete chosen-factor coordinate supplies the
opposite degree bound. -/
theorem
    exists_completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_exactNormalizationPrime
    {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A))) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    letI : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
              n a (fun _ ↦ hN) (fun _ ↦ hymax)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN) (fun _ ↦ hymax))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            letI : IsDomain Rn :=
              finiteEtaleResidueLift_pair_adjoinRoot_isDomain_exponentUnit
                y z hreg hgen hN
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            letI : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_faithful_exponentUnit eRoot
            letI : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBase_toSMul_isScalarTower_exponentUnit eRoot
            letI : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            letI : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebra_toSMul_isScalarTower_exponentUnit eRoot
            ∀ {K₀ L₀ : Type u} [Field K₀] [Field L₀]
              [Algebra K₀ KC] [Algebra K₀ L₀]
              [FiniteDimensional K₀ L₀] [IsGalois K₀ L₀],
              ∀ (m : Ideal (KC ⊗[K₀] L₀)) (hm : m.IsMaximal),
                letI : m.IsMaximal := hm
                let Omega := GenericTensorFieldComponent m
                letI : Algebra C Omega :=
                  ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
                letI : @IsScalarTower C KC Omega
                    (inferInstance : Algebra C KC).toSMul
                    (inferInstance : Algebra KC Omega).toSMul
                    (((algebraMap KC Omega).comp
                      (algebraMap C KC)).toAlgebra).toSMul :=
                  compositeAlgebra_toSMul_isScalarTower_exponentUnit
                ∀ [Algebra Omega P] [IsScalarTower KC Omega P],
                  let pC := Ideal.span ({yC} : Set C)
                  ∀ (Q : Ideal (integralClosure C Omega)) [Q.IsPrime]
                    [Q.LiesOver pC],
                    Q.ramificationIdx C = N →
                      (Localization.awayMap
                        (algebraMap C (integralClosure C Omega)) yC).Etale →
                        IsUnit (N : A) := by
  exact completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_exactNormalizationPrime
    y z hreg hgen N hN hCharZero

end EtaleFundamentalGroups.Kummer

end
