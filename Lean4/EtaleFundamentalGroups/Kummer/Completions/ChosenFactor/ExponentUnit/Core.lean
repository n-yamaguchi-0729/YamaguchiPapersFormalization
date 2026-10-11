/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Etale
import EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactorCoordinates
import EtaleFundamentalGroups.Kummer.IteratedRadical.Basic
import EtaleFundamentalGroups.Kummer.Descent.MultiAwayUnitDescent

/-!
# Exponent units from a complete-local chosen factor

This file combines the complete-local chosen-factor coordinates with
formal unramifiedness on the boundary complement.  It is the algebraic
consumer needed after the absolute Abhyankar construction has made the
chosen factor finite etale over the full iterated root cover.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators TensorProduct

universe u

/-- If `C / A` is faithfully flat, chosen-factor coordinates identify the iterated radical
extension over `C` with `D`, and the corresponding away algebra over the original ring `A`
is étale, then every radical exponent is already a unit in the original ring `A`. -/
theorem all_exponents_isUnit_of_iteratedRadical_chosenFactorCoordinates
    {A C D : Type u}
    [CommRing A] [IsDomain A]
    [CommRing C] [Algebra A C] [Module.FaithfullyFlat A C]
    [CommRing D] [Algebra A D] [Algebra C D] [IsScalarTower A C D]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i}))
    (e : iteratedRadical C r n (fun i ↦ algebraMap A C (a i)) ≃ₐ[C] D)
    (hAway : (Localization.awayMap (algebraMap A D)
      (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale) :
    ∀ i, IsUnit (n i : A) := by
  classical
  let fA : A := ∏ i ∈ (Finset.univ : Finset (Fin r)), a i
  let fC : C := algebraMap A C fA
  let fD : D := algebraMap A D fA
  let R := iteratedRadical C r n (fun i ↦ algebraMap A C (a i))
  let fR : R := algebraMap C R fC
  let S := Localization.Away fA
  let MC := Algebra.algebraMapSubmonoid C (Submonoid.powers fA)
  let T := Localization MC
  let U := Localization.Away fD
  let MR := Algebra.algebraMapSubmonoid R MC
  let Rₛ := Localization MR
  have hMC : MC = Submonoid.powers fC := by
    simp only [MC, fC, Algebra.algebraMapSubmonoid_powers]
  have hMR : MR = Submonoid.powers fR := by
    simp only [MR, hMC, fR, Algebra.algebraMapSubmonoid_powers]
  let : IsLocalization.Away fC T := by
    change IsLocalization (Submonoid.powers fC) T
    simpa only [fC, ← Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization MC T)
  let : IsLocalization.Away fR Rₛ := by
    change IsLocalization (Submonoid.powers fR) Rₛ
    rw [← hMR]
    exact
      (inferInstance : IsLocalization MR Rₛ)
  let mapST : S →+* T :=
    IsLocalization.Away.map S T (algebraMap A C) fA
  let mapCU : C →+* U := algebraMap C U
  have hCU : IsUnit (mapCU fC) := by
    have hACD : algebraMap C D fC = fD := by
      simpa [fC, fD] using
        (IsScalarTower.algebraMap_apply A C D fA).symm
    rw [show mapCU fC = algebraMap D U (algebraMap C D fC) by
      exact IsScalarTower.algebraMap_apply C D U fC]
    rw [hACD]
    exact IsLocalization.Away.algebraMap_isUnit _
  let mapTU : T →+* U := IsLocalization.Away.lift fC hCU
  let mapSU : S →+* U := Localization.awayMap (algebraMap A D) fA
  let : Algebra S T := mapST.toAlgebra
  let : Algebra T U := mapTU.toAlgebra
  let : Algebra S U := mapSU.toAlgebra
  have hSTU : mapTU.comp mapST = mapSU := by
    apply IsLocalization.ringHom_ext (Submonoid.powers fA)
    ext x
    change mapTU (mapST (algebraMap A S x)) =
      mapSU (algebraMap A S x)
    rw [show mapST (algebraMap A S x) =
        algebraMap C T (algebraMap A C x) by
      change IsLocalization.map T (algebraMap A C) _
        (algebraMap A S x) = algebraMap C T (algebraMap A C x)
      exact IsLocalization.map_eq _ x]
    rw [show mapTU (algebraMap C T (algebraMap A C x)) =
        mapCU (algebraMap A C x) by simp [mapTU]]
    rw [show mapSU (algebraMap A S x) = algebraMap A U x by
      change IsLocalization.map U (algebraMap A D) _
        (algebraMap A S x) = algebraMap D U (algebraMap A D x)
      exact IsLocalization.map_eq _ x]
    exact (IsScalarTower.algebraMap_apply A C U x).symm
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq' hSTU.symm
  let : Algebra.Etale S U := hAway.toAlgebra
  let : Algebra.FormallyUnramified T U :=
    Algebra.FormallyUnramified.of_restrictScalars S T U
  let mapCRₛ : C →+* Rₛ := algebraMap C Rₛ
  have hCRₛ : IsUnit (mapCRₛ fC) := by
    change IsUnit (algebraMap R Rₛ fR)
    exact IsLocalization.Away.algebraMap_isUnit _
  let mapTRₛ : T →+* Rₛ := IsLocalization.Away.lift fC hCRₛ
  have hmapTRₛ : mapTRₛ = algebraMap T Rₛ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers fC)
    ext x
    change mapTRₛ (algebraMap C T x) =
      algebraMap T Rₛ (algebraMap C T x)
    rw [show mapTRₛ (algebraMap C T x) = mapCRₛ x by
      simp [mapTRₛ]]
    exact IsScalarTower.algebraMap_apply C T Rₛ x
  have hmapPowers :
      Submonoid.map e (Submonoid.powers fR) = Submonoid.powers fD := by
    rw [Submonoid.map_powers]
    congr 1
    simpa [fR, fC, fD] using
      (e.commutes (algebraMap A C fA)).trans
        (IsScalarTower.algebraMap_apply A C D fA).symm
  let eLocC : Rₛ ≃ₐ[C] U :=
    IsLocalization.algEquivOfAlgEquiv Rₛ U e hmapPowers
  have hLocComm : eLocC.toRingHom.comp (algebraMap T Rₛ) = mapTU := by
    rw [← hmapTRₛ]
    apply IsLocalization.ringHom_ext (Submonoid.powers fC)
    ext x
    simp [eLocC, mapTRₛ, mapTU, mapCRₛ, mapCU]
  let eLocT : Rₛ ≃ₐ[T] U :=
    { toRingEquiv := eLocC.toRingEquiv
      commutes' := fun x ↦ DFunLike.congr_fun hLocComm x }
  let rootT :=
    iteratedRadical T r n
      (fun i ↦ algebraMap C T (algebraMap A C (a i)))
  let eBase : T ⊗[C] R ≃ₐ[T] rootT :=
    iteratedRadicalBaseChangeAlgEquiv n
      (fun i ↦ algebraMap A C (a i))
  let eTensorLoc : T ⊗[C] R ≃ₐ[T] Rₛ :=
    Localization.tensorRightAlgEquiv MC R
  let eRootLoc : rootT ≃ₐ[T] Rₛ := eBase.symm.trans eTensorLoc
  let eRootU : rootT ≃ₐ[T] U := eRootLoc.trans eLocT
  let : Algebra.FormallyUnramified T rootT :=
    Algebra.FormallyUnramified.of_equiv eRootU.symm
  have hfA : fA ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (haPrime i).ne_zero
  let : IsDomain S := IsLocalization.Away.isDomain S hfA
  let eST : S ⊗[A] C ≃ₐ[S] T := by
    exact Localization.tensorRightAlgEquiv (Submonoid.powers fA) C
  let : Module.FaithfullyFlat S T :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := S) (M := S ⊗[A] C) eST.symm.toLinearEquiv
  let : Nontrivial T :=
    (FaithfulSMul.algebraMap_injective S T).nontrivial
  have hnT : ∀ i, IsUnit (n i : T) :=
    all_exponents_isUnit_of_formallyUnramified_iteratedRadical
      (A := T) n
        (fun i ↦ algebraMap C T (algebraMap A C (a i))) hn
  have hnS : ∀ i, IsUnit (n i : S) := by
    intro i
    apply (isUnit_map_iff (algebraMap S T) (n i : S)).mp
    simpa using hnT i
  intro i
  exact isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
    (R := A) (S := S) Finset.univ a
    (fun j _ ↦ haPrime j) (fun j _ ↦ hCharZero j)
    (hn i) (by simpa using hnS i)

/--
Let `B / A` be the full positive iterated root cover of a complete local
ring.  If a finite etale `B`-algebra has a unique chosen closed-point factor
and its underlying `A`-algebra is etale on the boundary complement, then all
root exponents are units in `A`.

The finite residue lift and the generalized-Kummer coordinates of the chosen
factor are produced internally.  In particular, neither a tensor
presentation nor an exponent-unit hypothesis is part of the statement.
-/
theorem all_exponents_isUnit_of_completeChosenFactor
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haMax : ∀ i, a i ∈ IsLocalRing.maximalIdeal A)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i})) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a hn haMax
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        (∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) →
        (Localization.awayMap (algebraMap A D)
          (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale →
        ∀ i, IsUnit (n i : A) := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique hAway
  let B := iteratedRadical A r n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn haMax
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
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
      (residueFieldMap_bijective_iteratedRadical n a hn haMax)
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let C := FiniteEtaleResidueLift A l
  obtain ⟨eTensor, heCoord⟩ :=
    exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
      hmax n a hn haMax (D := D) q hunique
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
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
  obtain ⟨eCoord⟩ := heCoord
  exact all_exponents_isUnit_of_iteratedRadical_chosenFactorCoordinates
    n a hn haPrime hCharZero eCoord hAway

end EtaleFundamentalGroups.Kummer

end
