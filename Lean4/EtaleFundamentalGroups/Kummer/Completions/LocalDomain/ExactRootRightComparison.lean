/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Completions.Ramification.PrimeElementDivisibility
import EtaleFundamentalGroups.FiniteEtale.HenselianAscent
import EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExactRootFractionDegree
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.RightDomain

/-!
# Exact right comparison without a Noetherian complete base

The maximal-adic completion used in the selected-branch construction does
not currently carry a global `IsNoetherianRing` instance.  The exact-degree
sandwich only needs substantially less:

* the completed base is a complete local domain and its maximal ideal is
  finitely generated;
* the selected parameter is prime;
* the actual chosen factor is a domain.

The last item is concrete output of the retained normal chosen factor.  Its
tensor coordinate embeds the explicit finite-etale residue lift into that
factor, producing the lift's domain structure.  Finite-etale ascent produces
maximal-adic completeness of the lift.  Finally an exact normalization prime
over the mapped selected parameter produces its primality, and hence the DVR
needed for the Galois ramification divisibility theorem.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct

universe u

/-- A finite-etale local algebra over a complete local ring is complete for
its own maximal ideal, without a Noetherian hypothesis.

Freeness follows from flatness over a local base, so completeness transfers
through a finite basis.  Formal unramifiedness identifies the extended base
maximal ideal with the target maximal ideal. -/
theorem isAdicComplete_maximalIdeal_of_finiteEtale_local_without_noetherian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Module.Finite R S] [Algebra.Etale R S] :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  let : Module.Free R S := Module.free_of_flat_of_isLocalRing
  have hcomplete :
      IsAdicComplete (IsLocalRing.maximalIdeal R) S :=
    isAdicComplete_of_moduleFinite_of_moduleFree
      (I := IsLocalRing.maximalIdeal R) (M := S)
  have hm :
      (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
        IsLocalRing.maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hm]
  exact
    (ValuationTheory.DiscreteValuationField.isAdicComplete_map_algebraMap_iff
      (R := R) (S := S) (IsLocalRing.maximalIdeal R)).2 hcomplete

/-- The generic fraction field of a positive one-root domain has degree the
root exponent over the fraction field of the base.

Primality of the radicand is not needed once domainhood of the actual
one-root algebra is already source-produced by an equivalence with the
chosen normal factor. -/
theorem oneRoot_fractionRing_finrank_eq_exponent_of_domain
    {A K F : Type u}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (y : A)
    [IsDomain (AdjoinRoot (X ^ N - Polynomial.C y))]
    [Algebra (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [Algebra A F]
    [IsScalarTower A (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsScalarTower A K F] :
    Module.finrank K F = N := by
  let Rn := AdjoinRoot (X ^ N - Polynomial.C y)
  let : Module.Free A Rn :=
    (monic_X_pow_sub_C y hN.ne').free_adjoinRoot
  let : Module.Finite A Rn :=
    (monic_X_pow_sub_C y hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[A] Rn) :=
    Module.Finite.base_change A K Rn
  let eFinite : (K ⊗[A] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := A) (C := Rn) (K := K) (E := F)
  calc
    Module.finrank K F = Module.finrank K (K ⊗[A] Rn) :=
      eFinite.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank A Rn := Module.finrank_baseChange
    _ = (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C y hN.ne')).dim := by
      simpa only [Rn] using
        (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C y hN.ne')).finrank
    _ = (X ^ N - Polynomial.C y).natDegree := rfl
    _ = N := Polynomial.natDegree_X_pow_sub_C

/-- Finite-dimensionality companion to
`oneRoot_fractionRing_finrank_eq_exponent_of_domain`. -/
theorem oneRoot_fractionRing_finiteDimensional_of_domain
    {A K F : Type u}
    [CommRing A] [IsDomain A]
    [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (y : A)
    [IsDomain (AdjoinRoot (X ^ N - Polynomial.C y))]
    [Algebra (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [Algebra A F]
    [IsScalarTower A (AdjoinRoot (X ^ N - Polynomial.C y)) F]
    [IsScalarTower A K F] :
    FiniteDimensional K F := by
  let Rn := AdjoinRoot (X ^ N - Polynomial.C y)
  let : Module.Finite A Rn :=
    (monic_X_pow_sub_C y hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[A] Rn) :=
    Module.Finite.base_change A K Rn
  let eFinite : (K ⊗[A] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := A) (C := Rn) (K := K) (E := F)
  exact Module.Finite.equiv eFinite.toLinearEquiv

private theorem localFractionTarget_toSMul_faithful
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

private theorem localFractionTarget_toSMul_isScalarTower
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

private theorem localFractionAlgebra_toSMul_isScalarTower
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
    localFractionTarget_toSMul_faithful e
  let : Algebra (FractionRing C) (FractionRing D) :=
    fractionRingAlgebraOfAlgEquiv e
  exact FractionRing.isScalarTower_liftAlgebra C (FractionRing D)

private theorem compositeAlgebra_toSMul_isScalarTower
    {C KC Omega : Type u}
    [CommRing C] [CommRing KC] [CommRing Omega]
    [Algebra C KC] [Algebra KC Omega] :
    @IsScalarTower C KC Omega
      (inferInstance : Algebra C KC).toSMul
      (inferInstance : Algebra KC Omega).toSMul
      (((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra).toSMul := by
  let : Algebra C Omega :=
    ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  rw [RingHom.algebraMap_toAlgebra]

/-- Exact-normalization-prime degree sandwich for a complete local domain.

All comparison data are constructed in the theorem:

* the finite residue lift and the chosen tensor coordinate;
* domainhood and maximal-adic completeness of the residue lift;
* the exact root-field degree;
* the DVR at the literal normalization prime's contraction.

Thus neither Noetherianity/regularity of the completed base nor right-map
bijectivity or a field-degree comparison is a public input. -/
theorem
 exists_completeLocalDomainChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactNormalizationPrime
    {A : Type u}
    [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    (N : ℕ) (hN : 0 < N) (y : A) (hy : Prime y)
    (hCharZero : CharZero (A ⧸ Ideal.span ({y} : Set A))) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let B := iteratedRadical A 1 n a
    let hymax : y ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal y).mpr
        (mem_nonunits_iff.mpr hy.not_isUnit)
    let : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN) (fun _ ↦ hymax)
    ∀ {D : Type u} [CommRing D] [IsDomain D] [Algebra B D]
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
              hmax n a (fun _ ↦ hN) (fun _ ↦ hymax)
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
          let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let : IsDomain C := tensorChosenFactorRight_isDomain eTensor
            let yC := algebraMap A C y
            let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N y eTensor
            let : IsDomain Rn := eRoot.toMulEquiv.isDomain D
            let : Module.Free C Rn :=
              (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
            let : FaithfulSMul C Rn := inferInstance
            let P := FractionRing D
            let KC := FractionRing C
            let : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            let : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              localFractionTarget_toSMul_faithful eRoot
            let : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              localFractionTarget_toSMul_isScalarTower eRoot
            let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            let : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              localFractionAlgebra_toSMul_isScalarTower eRoot
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
                  compositeAlgebra_toSMul_isScalarTower
                ∀ [Algebra Omega P] [IsScalarTower KC Omega P],
                  let pC := Ideal.span ({yC} : Set C)
                  ∀ (Q : Ideal (integralClosure C Omega)) [Q.IsPrime]
                    [Q.LiesOver pC],
                    Q.ramificationIdx C = N →
                      Function.Bijective (algebraMap Omega P) := by
  intro n a B hymax localB D hCommD hDomainD algBD algAD towerABD finiteBD etaleBD
    q hqPrime hqOver hunique finiteAB flatAB integralAB localAB completeB
    localD localBD flatBD localAD k kB l eResidue finitekkB finitekl
    separablekkB separablekl C etaleAC
  have hn : ∀ i, 0 < n i := fun _ ↦ hN
  have ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A := fun _ ↦ hymax
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Module.FaithfullyFlat A C :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : IsAdicComplete (IsLocalRing.maximalIdeal C) C :=
    isAdicComplete_maximalIdeal_of_finiteEtale_local_without_noetherian
      (R := A) (S := C)
  let eTensor := Classical.choose
    (exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
      hmax n a hn ha (D := D) q hunique)
  refine ⟨eTensor, ?_⟩
  intro algCD domainC yC Rn eRoot domainRn freeRn faithfulRn P KC
    algCP faithfulCP towerCDP algKCP towerCKCP
  let Froot := FractionRing Rn
  let eRefl : Rn ≃ₐ[C] Rn := AlgEquiv.refl
  let : Algebra C Froot :=
    fractionRingTargetBaseAlgebraOfAlgEquiv eRefl
  let : @FaithfulSMul C Froot
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    localFractionTarget_toSMul_faithful eRefl
  let : @IsScalarTower C Rn Froot
      (inferInstance : Algebra C Rn).toSMul
      (inferInstance : Algebra Rn Froot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    localFractionTarget_toSMul_isScalarTower eRefl
  let : Algebra KC Froot := fractionRingAlgebraOfAlgEquiv eRefl
  let : @IsScalarTower C KC Froot
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRefl).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    localFractionAlgebra_toSMul_isScalarTower eRefl
  let eFrac : Froot ≃ₐ[KC] P :=
    IsFractionRing.fieldEquivOfAlgEquiv KC Froot P eRoot
  let : FiniteDimensional KC Froot :=
    oneRoot_fractionRing_finiteDimensional_of_domain
      (A := C) (K := KC) (F := Froot) hN yC
  let : FiniteDimensional KC P :=
    Module.Finite.equiv eFrac.toLinearEquiv
  have hRootDegree : Module.finrank KC Froot = N :=
    oneRoot_fractionRing_finrank_eq_exponent_of_domain
      (A := C) (K := KC) (F := Froot) hN yC
  have hDegree : Module.finrank KC P = N := by
    calc
      Module.finrank KC P = Module.finrank KC Froot :=
        eFrac.toLinearEquiv.finrank_eq.symm
      _ = N := hRootDegree
  intro K₀ L₀ hFieldK₀ hFieldL₀ algK₀KC algK₀L₀ finiteK₀L₀ galoisK₀L₀
    m hm hMax Omega algCOmega towerCKCOmega algOmegaP towerKCOmegaP
    pC Q hQPrime hQOver hExact
  let : pC.IsPrime := Ideal.isPrime_of_liesOver Q pC
  have hyCNe : yC ≠ 0 :=
    by
      simpa only [yC, map_zero] using
        (FaithfulSMul.algebraMap_injective A C).ne hy.ne_zero
  have hyC : Prime yC :=
    (Ideal.span_singleton_prime hyCNe).mp inferInstance
  let pA := Ideal.span ({y} : Set A)
  have hpMap : pA.map (algebraMap A C) = pC := by
    simp only [pA, pC, yC, Ideal.map_span, Set.image_singleton]
  have hCharCMap :
      CharZero (C ⧸ pA.map (algebraMap A C)) := by
    let J := pA.map (algebraMap A C)
    have hUnder : J.under A = pA :=
      Ideal.comap_map_eq_self_of_faithfullyFlat (B := C) pA
    let : CharZero (A ⧸ J.under A) := by
      rw [hUnder]
      exact hCharZero
    exact charZero_of_injective_algebraMap
      (Ideal.algebraMap_quotient_injective (R := A) (A := C) (I := J))
  let : CharZero (C ⧸ pC) := by
    rw [← hpMap]
    exact hCharCMap
  have hRamDiv : N ∣ Module.finrank KC Omega := by
    have hDiv : Q.ramificationIdx C ∣ Module.finrank KC Omega :=
      normalization_ramificationIdx_dvd_finrank_of_prime_isHausdorff
        (A := C) (K := KC) (L := Omega) yC hyC Q
    obtain ⟨d, hd⟩ := hDiv
    refine ⟨d, ?_⟩
    calc
      Module.finrank KC Omega = Q.ramificationIdx C * d := hd
      _ = N * d := by rw [hExact]
  let i : Omega →ₗ[KC] P :=
    (Algebra.linearMap Omega P).restrictScalars KC
  have hi : Function.Injective i := (algebraMap Omega P).injective
  have hOmegaLeP : Module.finrank KC Omega ≤ Module.finrank KC P :=
    i.finrank_le_finrank_of_injective hi
  have hRamLeOmega : N ≤ Module.finrank KC Omega :=
    Nat.le_of_dvd Module.finrank_pos hRamDiv
  have hFinrankEq : Module.finrank KC Omega = Module.finrank KC P := by
    omega
  have hiSurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hFinrankEq).mp hi
  refine ⟨(algebraMap Omega P).injective, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := hiSurjective z
  exact ⟨x, hx⟩

end EtaleFundamentalGroups.Kummer

end
