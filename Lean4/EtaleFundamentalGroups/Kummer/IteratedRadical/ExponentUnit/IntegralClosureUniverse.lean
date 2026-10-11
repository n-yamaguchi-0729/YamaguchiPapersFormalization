/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.IteratedRadical.EtaleFactorExponentUnit

/-!
# Universe-polymorphic exponent units from an etale normalization

This is the universe-polymorphic form of the terminal integral-closure
obstruction: the field containing the generic component need not live in the
same universe as the original base ring.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

open scoped TensorProduct

universe uA uD uL

/-- Universe-polymorphic terminal obstruction for a formally etale,
faithfully-flat factor of the iterated radical cover. -/
theorem all_exponents_isUnit_of_iteratedRadical_formallyEtaleFactor_universe
    {A : Type uA} [CommRing A] [IsDomain A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i})) :
    let B := iteratedRadical A r n a
    ∀ {D : Type uD} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Algebra.FormallyEtale B D] [Module.FaithfullyFlat B D],
      (Localization.awayMap (algebraMap A D)
        (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale →
      ∀ i, IsUnit (n i : A) := by
  dsimp only
  intro D _ _ _ _ _ _ hAway
  classical
  let B := iteratedRadical A r n a
  let fA : A := ∏ i ∈ (Finset.univ : Finset (Fin r)), a i
  let MA : Submonoid A := Submonoid.powers fA
  let MB : Submonoid B := Algebra.algebraMapSubmonoid B MA
  let MD : Submonoid D := Algebra.algebraMapSubmonoid D MB
  let MDA : Submonoid D := Algebra.algebraMapSubmonoid D MA
  let S := Localization MA
  let T := Localization MB
  let U := Localization MD
  have hMD : MD = MDA := by
    simp [MD, MDA, MB]
  let : IsLocalization MDA U := by
    rw [← hMD]
    infer_instance
  let : Algebra S U := localizationAlgebra MA D
  let : IsScalarTower A S U :=
    isScalarTower_localizationAlgebra MA D
  let : IsLocalization.Away (algebraMap A D fA) U := by
    change IsLocalization (Submonoid.powers (algebraMap A D fA)) U
    simpa only [MDA, MA, Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization MDA U)
  have hSTU :
      (algebraMap T U).comp (algebraMap S T) = algebraMap S U := by
    change
      (IsLocalization.map U (algebraMap B D) _).comp
          (IsLocalization.map T (algebraMap A B) _) =
        IsLocalization.map U (algebraMap A D) _
    rw [IsLocalization.map_comp_map]
    congr 1
    exact (IsScalarTower.algebraMap_eq A B D).symm
  let : IsScalarTower S T U :=
    IsScalarTower.of_algebraMap_eq' hSTU.symm
  have hAwayU : (algebraMap S U).Etale := by
    let AwayD := Localization.Away (algebraMap A D fA)
    let : Algebra S AwayD :=
      localizationAlgebra MA D
    let : IsScalarTower A S AwayD :=
      isScalarTower_localizationAlgebra MA D
    have hAwayS : (algebraMap S AwayD).Etale := by
      change (Localization.awayMap (algebraMap A D) fA).Etale
      exact hAway
    let : Algebra.Etale S AwayD := hAwayS.toAlgebra
    let eD : AwayD ≃ₐ[D] U :=
      IsLocalization.algEquiv
        (Submonoid.powers (algebraMap A D fA)) AwayD U
    have hcomm :
        eD.toRingHom.comp (algebraMap S AwayD) = algebraMap S U := by
      apply IsLocalization.ringHom_ext MA
      ext x
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A S AwayD,
        ← IsScalarTower.algebraMap_apply A S U,
        IsScalarTower.algebraMap_apply A D AwayD,
        IsScalarTower.algebraMap_apply A D U]
      exact eD.commutes (algebraMap A D x)
    let eS : AwayD ≃ₐ[S] U :=
      AlgEquiv.ofRingEquiv (f := eD.toRingEquiv) fun s ↦
        congrArg (fun k : S →+* U ↦ k s) hcomm
    let : Algebra.Etale S U := Algebra.Etale.of_equiv eS
    exact RingHom.etale_algebraMap.mpr inferInstance
  let : Algebra.Etale S U := hAwayU.toAlgebra
  let : IsLocalization (MB.map (algebraMap B D)) U := by
    change IsLocalization MD U
    infer_instance
  let : Algebra.FormallyEtale T U :=
    Algebra.FormallyEtale.localization_map
      (R := B) (S := D) (Rₘ := T) (Sₘ := U) MB
  let eTensor : T ⊗[B] D ≃ₐ[T] U :=
    Localization.tensorRightAlgEquiv MB D
  let : Module.FaithfullyFlat T U :=
    Module.FaithfullyFlat.of_linearEquiv
      (R := T) (M := T ⊗[B] D) eTensor.symm.toLinearEquiv
  let : Algebra.FormallyUnramified S T :=
    formallyUnramified_of_formallyEtale_faithfullyFlat
      (R := S) (S := T) (T := U)
  let rootS :=
    iteratedRadical S r n (fun i ↦ algebraMap A S (a i))
  let eBase : S ⊗[A] B ≃ₐ[S] rootS :=
    iteratedRadicalBaseChangeAlgEquiv n a
  let eTensorLoc : S ⊗[A] B ≃ₐ[S] T :=
    Localization.tensorRightAlgEquiv MA B
  let eRootT : rootS ≃ₐ[S] T := eBase.symm.trans eTensorLoc
  let : Algebra.FormallyUnramified S rootS :=
    Algebra.FormallyUnramified.of_equiv eRootT.symm
  have hfA : fA ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (haPrime i).ne_zero
  let : IsDomain S := IsLocalization.Away.isDomain S hfA
  have hnS : ∀ i, IsUnit (n i : S) :=
    all_exponents_isUnit_of_formallyUnramified_iteratedRadical
      (A := S) n (fun i ↦ algebraMap A S (a i)) hn
  intro i
  exact isUnit_natCast_of_isUnit_algebraMap_away_finsetProduct
    (R := A) (S := S) Finset.univ a
    (fun j _ ↦ haPrime j) (fun j _ ↦ hCharZero j)
    (hn i) (by simpa using hnS i)

/-- If the normalization of a positive iterated radical cover in a possibly
larger-universe field is etale, and its composite with the original base is
etale away from the whole boundary, every radical exponent is a unit in the
original base. -/
theorem all_exponents_isUnit_of_iteratedRadical_integralClosure_etale_universe
    {A : Type uA} [CommRing A] [IsDomain A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (haPrime : ∀ i, Prime (a i))
    (hCharZero : ∀ i, CharZero (A ⧸ Ideal.span {a i}))
    {L : Type uL} [Field L]
    [Algebra (iteratedRadical A r n a) L]
    [FaithfulSMul (iteratedRadical A r n a) L]
    (hEtale : Algebra.Etale
      (iteratedRadical A r n a)
      (integralClosure (iteratedRadical A r n a) L))
    (hAway : (Localization.awayMap
      ((algebraMap (iteratedRadical A r n a)
          (integralClosure (iteratedRadical A r n a) L)).comp
        (algebraMap A (iteratedRadical A r n a)))
      (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale) :
    ∀ i, IsUnit (n i : A) := by
  let B := iteratedRadical A r n a
  let D := integralClosure B L
  let mapAD : A →+* D := (algebraMap B D).comp (algebraMap A B)
  let : Algebra A D := mapAD.toAlgebra
  let : IsScalarTower A B D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale B D := hEtale
  let : FaithfulSMul B D :=
    (faithfulSMul_iff_algebraMap_injective B D).mpr <| by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective B L
      exact congrArg Subtype.val hxy
  let : Module.FaithfullyFlat B D := inferInstance
  change (Localization.awayMap (algebraMap A D)
    (∏ i ∈ (Finset.univ : Finset (Fin r)), a i)).Etale at hAway
  exact all_exponents_isUnit_of_iteratedRadical_formallyEtaleFactor_universe
    (A := A) n a hn haPrime hCharZero (D := D) hAway

end EtaleFundamentalGroups.Kummer

end
