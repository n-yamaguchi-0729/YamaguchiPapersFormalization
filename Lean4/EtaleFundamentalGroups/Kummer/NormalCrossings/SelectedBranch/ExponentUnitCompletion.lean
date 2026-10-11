/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import EtaleFundamentalGroups.Completions.Retained.ComponentToChosenLocalFraction
import EtaleFundamentalGroups.Completions.Retained.ComponentTower
import EtaleFundamentalGroups.Completions.Retained.NormalizationLocalRamification
import EtaleFundamentalGroups.Completions.Retained.PrefixBoundaryAway
import EtaleFundamentalGroups.Completions.Retained.RegularBranchPrimeChain
import EtaleFundamentalGroups.Completions.Retained.TensorPrimeContraction
import EtaleFundamentalGroups.Ramification.Tensor.FiniteFlat
import EtaleFundamentalGroups.LocalGeometry.DVR.FlatLocalAscent
import SchemeTheory.LocalGeometry.HeightOne.NormalLocalizationDVR
import EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.PrefixEmbedding.ExactPrimeBoundaryAway
import EtaleFundamentalGroups.Kummer.Completions.GenericTensorTower.ChosenFactorCompositumAway
import EtaleFundamentalGroups.Kummer.Completions.RegularLocal.ExactRootExponentUnit
import EtaleFundamentalGroups.Kummer.Completions.MaximalAdic.OneRootFiniteEtaleChosenFactor
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.SelectedComponent.ExactPrimeSource
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.FullRootCoverResidue

/-!
# The selected exponent from the retained completed component

The selected full-root component supplies a height-one/closed prime chain in
its finite normalization.  Maximal-adic completion retains that literal
chain.  Contracting it through the canonical intermediate normalization
selects the prefix component in the same completed factor.

The prefix component is then embedded in the fraction field of the retained
closed factor.  Its finite-etale residue-lift compositum carries both the
original boundary-Away statement and the exact selected ramification prime,
so the complete one-root terminal forces the exponent to be a unit.

Every component, prime, and comparison map used below is generated from the
single global component returned by the strict-normal-crossings source
theorem.  In particular, the statement exposes no completed component
comparison, right-coordinate bijectivity, or ramification-index hypothesis.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open Polynomial
open RingTheory.Sequence

universe u

/-- Close the exact-prime terminal after selecting the literal compositum
component determined by a prefix embedding.  Keeping this construction in a
separate opaque declaration prevents the actual-compositum definitions from
being unfolded while checking the much larger selected-branch proof below. -/
private theorem
    prefixEmbedding_exactPrimeBoundaryAway_terminal_isUnit
    {A C F KC M P : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Module.Finite A C] [Algebra.Etale A C] [FaithfulSMul A C]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field KC] [Algebra C KC] [IsFractionRing C KC]
    [Algebra A KC] [IsScalarTower A C KC]
    [Algebra F KC] [IsScalarTower A F KC]
    [Field M] [Algebra A M] [Algebra F M]
    [IsScalarTower A F M] [FiniteDimensional F M] [IsGalois F M]
    [Field P] [Algebra A P] [Algebra C P] [IsScalarTower A C P]
    [Algebra F P] [IsScalarTower A F P]
    [Algebra KC P] [IsScalarTower C KC P]
    [Module.Finite A (integralClosure A M)]
    (y z : A)
    (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞))
    (N : ℕ)
    (fPrefix : M →ₐ[F] P)
    (q : Ideal (integralClosure A M))
    (hqPrime : q.IsPrime)
    (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
    (hqExact : q.ramificationIdx A = N)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A M)) y).Etale)
    (hTerminal :
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
            by
              refine @IsScalarTower.of_algebraMap_eq C KC Omega
                _ _ _ (inferInstance : Algebra C KC)
                  (inferInstance : Algebra KC Omega)
                  (((algebraMap KC Omega).comp
                    (algebraMap C KC)).toAlgebra) ?_
              intro x
              rfl
          ∀ [Algebra Omega P] [IsScalarTower KC Omega P],
            let pC := Ideal.span ({algebraMap A C y} : Set C)
            ∀ (Q : Ideal (integralClosure C Omega)) [Q.IsPrime]
              [Q.LiesOver pC],
              Q.ramificationIdx C = N →
                (Localization.awayMap
                  (algebraMap C (integralClosure C Omega))
                  (algebraMap A C y)).Etale →
                  IsUnit (N : A)) :
    IsUnit (N : A) := by
  classical
  obtain
      ⟨mKC, hmKC, omegaToP, hTowerCKCOmega, hTowerOmega,
        hAwayOmega, QOmega, hQOmegaPrime, hQOmegaOver, hQOmegaExact⟩ :=
    completeRegularPair_prefixEmbedding_actualCompositum_exactPrime_boundaryAway
      (A := A) (C := C) (F := F) (KC := KC) (M := M) (P := P)
      y z hreg hgen hdim N fPrefix q hqPrime hqOver hqExact hAway
  let Omega := GenericTensorFieldComponent mKC
  let cOmegaAlgebra : Algebra C Omega :=
    ((algebraMap KC Omega).comp (algebraMap C KC)).toAlgebra
  let : Algebra Omega P := omegaToP.toRingHom.toAlgebra
  exact hTerminal (K₀ := F) (L₀ := M)
    mKC hmKC QOmega hQOmegaExact hAwayOmega

/-- Produce only the domain/DVR facts needed from the retained vertical
localization.  The localization algebra and flatness instances stay inside
this small scope. -/
private theorem selectedExponent_prefix_localization_dvr
    {R S R' : Type u}
    [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    [IsDomain S] [IsIntegrallyClosed S] [IsNoetherianRing S]
    [hR'Noetherian : IsNoetherianRing R']
    [Module.Finite R S] [Module.Flat R R']
    (y : R)
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span ({y} : Set R))]
    (Q : Ideal (R' ⊗[R] S)) [hQPrime : Q.IsPrime]
    [_hQBranch : Q.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R'))]
    (hQRight :
      Q.comap Algebra.TensorProduct.includeRight.toRingHom = q)
    (hqHeight : q.height = 1)
    [hCharZero : CharZero (R ⧸ Ideal.span ({y} : Set R))] :
    ∃ _hWDomain : IsDomain (Localization.AtPrime Q),
      IsDiscreteValuationRing (Localization.AtPrime Q) := by
  classical
  let T := R' ⊗[R] S
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let hQOver : Q.LiesOver q :=
    (Ideal.liesOver_iff Q q).mpr hQRight.symm
  let V := Localization.AtPrime q
  let W := Localization.AtPrime Q
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_normal_noetherian_height_one
      q hqHeight
  let : Module.Finite R' T := Module.Finite.base_change R R' S
  let hTNoetherian : IsNoetherianRing T :=
    IsNoetherianRing.of_finite R' T
  let : IsNoetherianRing W :=
    IsLocalization.isNoetherianRing Q.primeCompl W hTNoetherian
  let comm : (S ⊗[R] R') ≃ₐ[S] T :=
    Algebra.TensorProduct.commRight R S R'
  let : Module.Flat S T :=
    Module.Flat.of_linearEquiv comm.symm.toLinearEquiv
  let : Algebra V W := Localization.AtPrime.algebraOfLiesOver q Q
  let hWFlat : Module.Flat V W := by
    rw [Module.flat_iff_of_isLocalization V q.primeCompl]
    exact Module.Flat.trans S T W
  let : IsLocalHom (algebraMap V W) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom
      q Q (algebraMap S T) Ideal.LiesOver.over
  have hmaxRight : q.map (algebraMap S W) = maximalIdeal W :=
    tensorProduct_localization_right_maximalIdeal_eq_span_of_finite_flat_charZero
      (R := R) (S := S) (R' := R') y q Q hQRight
  have hmaxLocal :
      (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
    calc
      (maximalIdeal V).map (algebraMap V W) =
          (q.map (algebraMap S V)).map (algebraMap V W) := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
      _ = q.map (algebraMap S W) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq S V W]
      _ = maximalIdeal W := hmaxRight
  exact
    exists_isDomain_isDiscreteValuationRing_of_flat_local_of_map_maximalIdeal_eq
      (V := V) (W := W) hmaxLocal

/-- Opaque output of the first completed-prime stage.  All completed tensor
coordinates are deterministic; only the retained chain is stored. -/
private def SelectedCompletedPrimeChainPackage
    {B E : Type u}
    [CommRing B] [IsLocalRing B]
    [CommRing E] [Algebra B E]
    (yB : B) (qGlobal p : Ideal E) : Prop :=
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  let Tfinal := Bhat ⊗[B] E
  let Pfinal := p.map
    (Algebra.TensorProduct.includeRight
      (R := B) (A := Bhat) (B := E)).toRingHom
  ∃ Nfinal Qfinal : Ideal Tfinal,
    Nfinal ≤ Qfinal ∧ Nfinal ≤ Pfinal ∧
      Nfinal.IsPrime ∧
      Nfinal.comap
        (Algebra.TensorProduct.includeLeftRingHom
          (R := B) (A := Bhat) (B := E)) =
        (⊥ : Ideal Bhat) ∧
      Qfinal.IsPrime ∧
      Qfinal.comap
        (Algebra.TensorProduct.includeRight
          (R := B) (A := Bhat) (B := E)).toRingHom = qGlobal ∧
      Qfinal.comap
        (Algebra.TensorProduct.includeLeftRingHom
          (R := B) (A := Bhat) (B := E)) =
        Ideal.span ({yhat} : Set Bhat) ∧
      Pfinal.IsMaximal

/-- Produce the retained completed prime chain before any prefix contraction
or normalization instances are introduced. -/
private theorem selectedExponent_completed_prime_chain_source
    {B E : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing E] [Algebra B E] [Module.Flat B E]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (qGlobal p : Ideal E)
    (hqGlobalPrime : qGlobal.IsPrime)
    (hqGlobalOverB : qGlobal.LiesOver (Ideal.span ({yB} : Set B)))
    (hqGlobalLe : qGlobal ≤ p)
    (hpMax : p.IsMaximal)
    (hpOverB : p.LiesOver (maximalIdeal B)) :
    SelectedCompletedPrimeChainPackage yB qGlobal p := by
  classical
  let qB := Ideal.span ({yB} : Set B)
  let : qGlobal.LiesOver qB := by simpa only [qB] using hqGlobalOverB
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  have hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  let : IsDomain Bhat := hgeometryHat.1
  let : IsNoetherianRing Bhat :=
    maximalAdicCompletion_isNoetherianRing_of_regularPair hregB hgenB
  let Tfinal := Bhat ⊗[B] E
  let : Algebra Bhat Tfinal := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Tfinal := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B Bhat Tfinal :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower B E Tfinal :=
    Algebra.TensorProduct.right_isScalarTower
  let Pfinal := p.map (algebraMap E Tfinal)
  obtain
      ⟨Nfinal, Qfinal, hNfinalQfinal, hQfinalP,
        hNfinalPrime, hNfinalOver, hQfinalPrime, hQfinalOver,
        hQfinalBranch, hPfinalMax, -⟩ :=
    exists_adicCompletion_genericPrime_le_regularBranch_le_retainedClosedPrime
      (R := B) (S := E) hregB hgenB qGlobal p hqGlobalLe
        (qGlobal.over_def qB).symm
  unfold SelectedCompletedPrimeChainPackage
  exact ⟨Nfinal, Qfinal, hNfinalQfinal,
    le_trans hNfinalQfinal hQfinalP, hNfinalPrime,
    hNfinalOver.over.symm, hQfinalPrime, hQfinalOver.over.symm,
    hQfinalBranch.over.symm, hPfinalMax⟩

/-- Contract the retained completed chain and compute its exact boundary
index in a fresh tensor context. -/
private theorem selectedExponent_contracted_prefix_source
    {R R' S₀ S₁ : Type u}
    [CommRing R] [CommRing R'] [CommRing S₀] [CommRing S₁]
    [Algebra R R'] [Algebra R S₀] [Algebra R S₁]
    [Module.Finite R S₀] [Module.Flat R R']
    (y : R)
    (q₀ : Ideal S₀) [_hq₀Prime : q₀.IsPrime]
    [_hq₀Over : q₀.LiesOver (Ideal.span ({y} : Set R))]
    (g : S₀ →ₐ[R] S₁)
    (q₁ : Ideal S₁) [_hq₁Prime : q₁.IsPrime]
    (hq₁q₀ : q₁.comap g.toRingHom = q₀)
    (N Q : Ideal (R' ⊗[R] S₁))
    [_hNPrime : N.IsPrime] [_hNOver : N.LiesOver (⊥ : Ideal R')]
    [_hQPrime : Q.IsPrime]
    (hQq₁ : Q.comap
      (Algebra.TensorProduct.includeRight
        (R := R) (A := R') (B := S₁)).toRingHom = q₁)
    [hQBranch : Q.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R'))]
    (hNQ : N ≤ Q)
    [hCharZero : CharZero (R ⧸ Ideal.span ({y} : Set R))]
    {e : ℕ} (hq₀Exact : q₀.ramificationIdx R = e) :
    let f := completedFiniteModelTowerAlgHom
      (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
    let N₀ := N.comap f.toRingHom
    let Q₀ := Q.comap f.toRingHom
    N₀ ≤ Q₀ ∧ N₀.IsPrime ∧
      N₀.LiesOver (⊥ : Ideal R') ∧
      Q₀.IsPrime ∧ Q₀.LiesOver
        (Ideal.span ({algebraMap R R' y} : Set R')) ∧
      Q₀.comap
        (Algebra.TensorProduct.includeRight
          (R := R) (A := R') (B := S₀)).toRingHom = q₀ ∧
      Q₀.ramificationIdx R' = e := by
  classical
  dsimp only
  let : Algebra S₁ (R' ⊗[R] S₁) :=
    Algebra.TensorProduct.rightAlgebra
  have hQOver : Q.LiesOver q₁ :=
    (Ideal.liesOver_iff Q q₁).mpr hQq₁.symm
  let f := completedFiniteModelTowerAlgHom
    (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁) g
  let N₀ := N.comap f.toRingHom
  let Q₀ := Q.comap f.toRingHom
  obtain
      ⟨hN₀Q₀, hN₀Prime, hN₀Over, hQ₀Prime, hQ₀Over⟩ :=
    completedFiniteModelTower_contract_primeChain
      (R := R) (R' := R') (S₀ := S₀) (S₁ := S₁)
      g q₀ q₁ hq₁q₀ N Q hNQ
  let : Algebra S₀ (R' ⊗[R] S₀) :=
    Algebra.TensorProduct.rightAlgebra
  have hQ₀Branch : Q₀.LiesOver
      (Ideal.span ({algebraMap R R' y} : Set R')) := by
    constructor
    calc
      Ideal.span ({algebraMap R R' y} : Set R') = Q.under R' :=
        hQBranch.over
      _ = Q₀.under R' := by
        ext x
        change algebraMap R' (R' ⊗[R] S₁) x ∈ Q ↔
          f (algebraMap R' (R' ⊗[R] S₀) x) ∈ Q
        rw [f.commutes x]
  have hQ₀Right :
      Q₀.comap Algebra.TensorProduct.includeRight.toRingHom = q₀ := by
    change Q₀.comap (algebraMap S₀ (R' ⊗[R] S₀)) = q₀
    exact (Q₀.over_def q₀).symm
  have hQ₀Exact : Q₀.ramificationIdx R' = e :=
    ramificationIdx_tensorProduct_span_eq_of_finite_flat_charZero_of_eq
      (R := R) (S := S₀) (R' := R')
      (y := y) (q := q₀) (Q := Q₀) hQ₀Right hq₀Exact
  exact ⟨hN₀Q₀, hN₀Prime, hN₀Over, hQ₀Prime,
    hQ₀Branch, hQ₀Right, hQ₀Exact⟩

/-- Narrow dependent output of the retained prefix-normalization leaf.
The inductive wrapper keeps the source theorem's target opaque while its sole
field records the source-produced prime and boundary facts. -/
private inductive SelectedPrefixNormalizationPackage
    {B KB M₀ : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀]
    [Algebra KB M₀] [IsScalarTower B KB M₀]
    [FiniteDimensional KB M₀] [Algebra.IsSeparable KB M₀]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [IsIntegrallyClosed (integralClosure B M₀)]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (e : ℕ)
    (Nprefix : Ideal
      ((AdicCompletion (maximalIdeal B) B) ⊗[B]
        (integralClosure B M₀)))
    [Nprefix.IsPrime]
    [Nprefix.LiesOver
      (⊥ : Ideal (AdicCompletion (maximalIdeal B) B))] : Prop where
  | mk :
      (let C₀ := integralClosure B M₀
       let Bhat := AdicCompletion (maximalIdeal B) B
       let hgeometryHat :=
         maximalAdicCompletion_regularPair_geometry hregB hgenB
       letI : IsDomain Bhat := hgeometryHat.1
       letI : IsNoetherianRing Bhat :=
         maximalAdicCompletion_isNoetherianRing_of_regularPair hregB hgenB
       let Khat := FractionRing Bhat
       letI : Module.FaithfullyFlat B Bhat :=
         Module.FaithfullyFlat.of_flat_of_isLocalHom
       letI : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
       letI : Algebra KB Khat :=
         (IsFractionRing.lift
           (A := B) (K := KB) (L := Khat)
           (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
       letI : IsScalarTower B KB Khat :=
         IsScalarTower.of_algebraMap_smul fun b x ↦ by
           rw [Algebra.smul_def, Algebra.smul_def]
           change
             (IsFractionRing.lift
               (A := B) (K := KB) (L := Khat)
               (FaithfulSMul.algebraMap_injective B Khat))
                 (algebraMap B KB b) * x =
               algebraMap B Khat b * x
           rw [IsFractionRing.lift_algebraMap]
       let mPrefix := retainedCompletedGenericTensorIdeal
         (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
         (K' := Khat) Nprefix
       letI : mPrefix.IsMaximal :=
         retainedCompletedGenericTensorIdeal_isMaximal
           (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
           (K' := Khat) Nprefix
       let OmegaPrefix := GenericTensorFieldComponent mPrefix
       let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
         genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
       letI : Algebra Bhat OmegaPrefix := bHatOmegaPrefixAlgebra
       letI : SMul Bhat OmegaPrefix := bHatOmegaPrefixAlgebra.toSMul
       letI : IsScalarTower Bhat Khat OmegaPrefix :=
         IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
       ∃ qhatPrefix : Ideal (integralClosure Bhat OmegaPrefix),
         ∃ hqhatPrime : qhatPrefix.IsPrime,
           letI : qhatPrefix.IsPrime := hqhatPrime
           ∃ hqhatOver : qhatPrefix.LiesOver
               (Ideal.span ({algebraMap B Bhat yB} : Set Bhat)),
             letI : qhatPrefix.LiesOver
                 (Ideal.span ({algebraMap B Bhat yB} : Set Bhat)) := hqhatOver
             qhatPrefix.ramificationIdx Bhat = e ∧
               (Localization.awayMap
                 (algebraMap Bhat (integralClosure Bhat OmegaPrefix))
                 (algebraMap B Bhat yB)).Etale) →
      SelectedPrefixNormalizationPackage yB zB hregB hgenB e Nprefix

/-- Opaque name for the literal retained-prefix normalization ring. -/
private noncomputable def selectedPrefixNormalizationRing
    {B KB M₀ : Type u}
    [hBComm : CommRing B] [hBDomain : IsDomain B]
    [hBRegular : IsRegularLocalRing B]
    [hKBField : Field KB] [hBKB : Algebra B KB]
    [hKBFrac : IsFractionRing B KB]
    [hM₀Field : Field M₀] [hBM₀ : Algebra B M₀]
    [hKBM₀ : Algebra KB M₀] [hBKBM₀ : IsScalarTower B KB M₀]
    [hBC₀M₀ : IsScalarTower B (integralClosure B M₀) M₀]
    [hC₀Finite : Module.Finite B (integralClosure B M₀)]
    [hC₀Frac : IsFractionRing (integralClosure B M₀) M₀]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (Nprefix : Ideal
      ((AdicCompletion (maximalIdeal B) B) ⊗[B]
        (integralClosure B M₀)))
    [hNprefixPrime : Nprefix.IsPrime]
    [hNprefixOver : Nprefix.LiesOver
      (⊥ : Ideal (AdicCompletion (maximalIdeal B) B))] : Type u :=
  let C₀ := integralClosure B M₀
  let Bhat := AdicCompletion (maximalIdeal B) B
  let hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  letI : IsDomain Bhat := hgeometryHat.1
  let Khat := FractionRing Bhat
  letI : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  letI : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  letI : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let mPrefix := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
    (K' := Khat) Nprefix
  letI : mPrefix.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix
  let OmegaPrefix := GenericTensorFieldComponent mPrefix
  let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
  letI : Algebra Bhat OmegaPrefix := bHatOmegaPrefixAlgebra
  integralClosure Bhat OmegaPrefix

/-- Small owner-explicit carrier for the normalization prime produced by the
fresh prefix leaf.  It is independent of the finite-model construction. -/
private structure SelectedAlgebraOwner
    (R Ω : Type u) [CommRing R] where
  commRingΩ : CommRing Ω
  algebra :
    letI : CommRing Ω := commRingΩ
    Algebra R Ω

/-- The canonical algebra owner for the opaque retained-prefix normalization
ring. -/
private noncomputable def selectedPrefixNormalizationOwner
    {B KB M₀ : Type u}
    [hBComm : CommRing B] [hBDomain : IsDomain B]
    [hBRegular : IsRegularLocalRing B]
    [hKBField : Field KB] [hBKB : Algebra B KB]
    [hKBFrac : IsFractionRing B KB]
    [hM₀Field : Field M₀] [hBM₀ : Algebra B M₀]
    [hKBM₀ : Algebra KB M₀] [hBKBM₀ : IsScalarTower B KB M₀]
    [hBC₀M₀ : IsScalarTower B (integralClosure B M₀) M₀]
    [hC₀Finite : Module.Finite B (integralClosure B M₀)]
    [hC₀Frac : IsFractionRing (integralClosure B M₀) M₀]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (Nprefix : Ideal
      ((AdicCompletion (maximalIdeal B) B) ⊗[B]
        (integralClosure B M₀)))
    [hNprefixPrime : Nprefix.IsPrime]
    [hNprefixOver : Nprefix.LiesOver
      (⊥ : Ideal (AdicCompletion (maximalIdeal B) B))] :
    SelectedAlgebraOwner
      (AdicCompletion (maximalIdeal B) B)
      (selectedPrefixNormalizationRing
        (hBComm := hBComm) (hBDomain := hBDomain)
        (hBRegular := hBRegular) (hKBField := hKBField)
        (hBKB := hBKB) (hKBFrac := hKBFrac)
        (hM₀Field := hM₀Field) (hBM₀ := hBM₀)
        (hKBM₀ := hKBM₀) (hBKBM₀ := hBKBM₀)
        (hBC₀M₀ := hBC₀M₀) (hC₀Finite := hC₀Finite)
        (hC₀Frac := hC₀Frac)
        (hNprefixPrime := hNprefixPrime) (hNprefixOver := hNprefixOver)
        yB zB hregB hgenB Nprefix) := by
  let C₀ := integralClosure B M₀
  let Bhat := AdicCompletion (maximalIdeal B) B
  let hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  letI : IsDomain Bhat := hgeometryHat.1
  let Khat := FractionRing Bhat
  letI : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  letI : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  letI : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let mPrefix := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
    (K' := Khat) Nprefix
  letI : mPrefix.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix
  let OmegaPrefix := GenericTensorFieldComponent mPrefix
  let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
  letI : Algebra Bhat OmegaPrefix := bHatOmegaPrefixAlgebra
  refine ⟨?_, ?_⟩
  · change CommRing (integralClosure Bhat OmegaPrefix)
    infer_instance
  · change Algebra Bhat (integralClosure Bhat OmegaPrefix)
    exact (integralClosure Bhat OmegaPrefix).algebra

private inductive SelectedPrefixNormalizationOutput
    {R Ω : Type u} [CommRing R]
    (a : SelectedAlgebraOwner R Ω) (y : R) (e : ℕ) : Prop where
  | mk :
      (letI : CommRing Ω := a.commRingΩ
       letI : Algebra R Ω := a.algebra
       ∃ q : Ideal Ω,
         ∃ hqPrime : q.IsPrime,
           letI : q.IsPrime := hqPrime
           ∃ hqOver : q.LiesOver (Ideal.span ({y} : Set R)),
             letI : q.LiesOver (Ideal.span ({y} : Set R)) := hqOver
             q.ramificationIdx R = e ∧
               (Localization.awayMap (algebraMap R Ω) y).Etale) →
      SelectedPrefixNormalizationOutput a y e

/-- Lift the contracted retained prime to the selected normalization and
transport the boundary-Away statement in a fresh normalization context. -/
private theorem selectedExponent_prefix_normalization_source
    {B KB M₀ : Type u}
    [hBComm : CommRing B] [hBDomain : IsDomain B]
    [hBRegular : IsRegularLocalRing B]
    [hKBField : Field KB] [hBKB : Algebra B KB]
    [hKBFrac : IsFractionRing B KB]
    [hM₀Field : Field M₀] [hBM₀ : Algebra B M₀]
    [hKBM₀ : Algebra KB M₀] [hBKBM₀ : IsScalarTower B KB M₀]
    [hFinKBM₀ : FiniteDimensional KB M₀]
    [hSepKBM₀ : Algebra.IsSeparable KB M₀]
    [hBC₀M₀ : IsScalarTower B (integralClosure B M₀) M₀]
    [hC₀Finite : Module.Finite B (integralClosure B M₀)]
    [hC₀Frac : IsFractionRing (integralClosure B M₀) M₀]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (e : ℕ)
    (Nprefix Qprefix : Ideal
      ((AdicCompletion (maximalIdeal B) B) ⊗[B]
        (integralClosure B M₀)))
    [_hNprefixPrime : Nprefix.IsPrime]
    [_hNprefixOver : Nprefix.LiesOver
      (⊥ : Ideal (AdicCompletion (maximalIdeal B) B))]
    [_hQprefixPrime : Qprefix.IsPrime]
    [hQprefixBranch : Qprefix.LiesOver
      (Ideal.span
        ({algebraMap B (AdicCompletion (maximalIdeal B) B) yB} :
          Set (AdicCompletion (maximalIdeal B) B)))]
    (hNprefixQprefix : Nprefix ≤ Qprefix)
    [_hWprefixDomain : IsDomain (Localization.AtPrime Qprefix)]
    [_hWprefixDVR : IsDiscreteValuationRing (Localization.AtPrime Qprefix)]
    (hQprefixExact :
      Qprefix.ramificationIdx (AdicCompletion (maximalIdeal B) B) = e)
    (hAwayPrefix :
      (Localization.awayMap
        (algebraMap B (integralClosure B M₀)) yB).Etale) :
    SelectedPrefixNormalizationOutput
      (R := AdicCompletion (maximalIdeal B) B)
      (Ω := selectedPrefixNormalizationRing
        (hBComm := hBComm) (hBDomain := hBDomain)
        (hBRegular := hBRegular) (hKBField := hKBField)
        (hBKB := hBKB) (hKBFrac := hKBFrac)
        (hM₀Field := hM₀Field) (hBM₀ := hBM₀)
        (hKBM₀ := hKBM₀) (hBKBM₀ := hBKBM₀)
        (hBC₀M₀ := hBC₀M₀) (hC₀Finite := hC₀Finite)
        (hC₀Frac := hC₀Frac)
        (hNprefixPrime := _hNprefixPrime)
        (hNprefixOver := _hNprefixOver)
        yB zB hregB hgenB Nprefix)
      (selectedPrefixNormalizationOwner
        (hBComm := hBComm) (hBDomain := hBDomain)
        (hBRegular := hBRegular) (hKBField := hKBField)
        (hBKB := hBKB) (hKBFrac := hKBFrac)
        (hM₀Field := hM₀Field) (hBM₀ := hBM₀)
        (hKBM₀ := hKBM₀) (hBKBM₀ := hBKBM₀)
        (hBC₀M₀ := hBC₀M₀) (hC₀Finite := hC₀Finite)
        (hC₀Frac := hC₀Frac)
        (hNprefixPrime := _hNprefixPrime)
        (hNprefixOver := _hNprefixOver)
        yB zB hregB hgenB Nprefix)
      (algebraMap B (AdicCompletion (maximalIdeal B) B) yB) e := by
  classical
  let C₀ := integralClosure B M₀
  let Bhat := AdicCompletion (maximalIdeal B) B
  let hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  let : IsDomain Bhat := hgeometryHat.1
  let : IsNoetherianRing Bhat :=
    maximalAdicCompletion_isNoetherianRing_of_regularPair hregB hgenB
  let Khat := FractionRing Bhat
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  let : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  let : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let mPrefix := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
    (K' := Khat) Nprefix
  let : mPrefix.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix
  let OmegaPrefix := GenericTensorFieldComponent mPrefix
  let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
  let : SMul Bhat OmegaPrefix := bHatOmegaPrefixAlgebra.toSMul
  let : IsScalarTower Bhat Khat OmegaPrefix :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Tprefix := Bhat ⊗[B] C₀
  let : Algebra Bhat Tprefix := Algebra.TensorProduct.leftAlgebra
  let : Algebra C₀ Tprefix := Algebra.TensorProduct.rightAlgebra
  let ICprefix := integralClosure Bhat OmegaPrefix
  let jPrefix : Tprefix →ₐ[Bhat] ICprefix :=
    retainedCompletedChosenNormalizationAlgHom
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix
  let : Algebra Tprefix ICprefix := jPrefix.toAlgebra
  let : IsScalarTower Bhat Tprefix ICprefix :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (jPrefix.commutes x).symm
  let : Algebra.IsIntegral Bhat ICprefix := by
    change Algebra.IsIntegral Bhat (integralClosure Bhat OmegaPrefix)
    exact integralClosure.AlgebraIsIntegral
  let : Algebra.IsIntegral Tprefix ICprefix :=
    Algebra.IsIntegral.tower_top (S := Tprefix) (T := ICprefix) Bhat
  have hkerPrefix : RingHom.ker (algebraMap Tprefix ICprefix) ≤ Qprefix := by
    change RingHom.ker
      (retainedCompletedChosenNormalizationAlgHom
        (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
        (K' := Khat) Nprefix).toRingHom ≤ Qprefix
    rw [retainedCompletedChosenNormalizationAlgHom_ker
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix]
    exact hNprefixQprefix
  obtain ⟨qhatPrefix, -, hqhatPrefixPrime, hqhatPrefixComap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral
      Qprefix (⊥ : Ideal ICprefix) hkerPrefix
  have hqhatPrefixOver : qhatPrefix.LiesOver Qprefix :=
    (Ideal.liesOver_iff qhatPrefix Qprefix).mpr hqhatPrefixComap.symm
  have hqhatPrefixOverBranch : qhatPrefix.LiesOver
      (Ideal.span ({algebraMap B Bhat yB} : Set Bhat)) :=
    Ideal.LiesOver.trans qhatPrefix Qprefix
      (Ideal.span ({algebraMap B Bhat yB} : Set Bhat))
  obtain ⟨-, hqhatPrefixExactQ⟩ :=
    retainedCompletedNormalizationAtPrime_localAlgEquiv_and_ramificationIdx_eq
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix Qprefix hNprefixQprefix qhatPrefix
  have hqhatPrefixExact : qhatPrefix.ramificationIdx Bhat = e :=
    hqhatPrefixExactQ.trans hQprefixExact
  have hAwayPrefixHat :=
    retainedCompletedPrefix_normalization_boundaryAway
      (B := B) (K := KB) (M := M₀)
      yB zB hregB hgenB hdimB Nprefix hAwayPrefix
  dsimp only at hAwayPrefixHat
  have hResult :
      ∃ qhatPrefix : Ideal ICprefix,
        ∃ hqhatPrime : qhatPrefix.IsPrime,
          letI : qhatPrefix.IsPrime := hqhatPrime
          ∃ hqhatOver : qhatPrefix.LiesOver
              (Ideal.span ({algebraMap B Bhat yB} : Set Bhat)),
            letI : qhatPrefix.LiesOver
                (Ideal.span ({algebraMap B Bhat yB} : Set Bhat)) := hqhatOver
            qhatPrefix.ramificationIdx Bhat = e ∧
              (Localization.awayMap
                (algebraMap Bhat ICprefix)
                (algebraMap B Bhat yB)).Etale := by
    refine ⟨qhatPrefix, hqhatPrefixPrime, hqhatPrefixOverBranch, ?_⟩
    exact ⟨hqhatPrefixExact, hAwayPrefixHat⟩
  apply SelectedPrefixNormalizationOutput.mk
  exact hResult

/-- The narrow noncanonical output of the completed-prefix construction.
All tensor products, contractions, and component fields are deterministic
from `Nfinal`; only the two retained primes and their mathematical facts are
stored. -/
private def SelectedExponentPrefixPackageBody
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [Algebra B (integralClosure D M)]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (N : ℕ)
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (p : Ideal (integralClosure D M)) : Prop :=
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  let hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  letI : IsDomain Bhat := hgeometryHat.1
  let Khat := FractionRing Bhat
  let hBhatFaithfullyFlat : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  letI : Module.FaithfullyFlat B Bhat := hBhatFaithfullyFlat
  letI : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  let kBKhatAlgebra : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  letI : Algebra KB Khat := kBKhatAlgebra
  let kBKhatTower : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  letI : IsScalarTower B KB Khat := kBKhatTower
  let E := integralClosure D M
  let C₀ := integralClosure B M₀
  let Tfinal := Bhat ⊗[B] E
  letI : Algebra Bhat Tfinal := Algebra.TensorProduct.leftAlgebra
  letI : Algebra E Tfinal := Algebra.TensorProduct.rightAlgebra
  let Pfinal := p.map (algebraMap E Tfinal)
  ∃ Nfinal : Ideal Tfinal,
    ∃ hNfinalPrime : Nfinal.IsPrime,
      ∃ hNfinalOver : Nfinal.LiesOver (⊥ : Ideal Bhat),
      letI : Nfinal.IsPrime := hNfinalPrime
      letI : Nfinal.LiesOver (⊥ : Ideal Bhat) := hNfinalOver
      Nfinal ≤ Pfinal ∧ Pfinal.IsMaximal ∧
      let Tprefix := Bhat ⊗[B] C₀
      letI : Algebra Bhat Tprefix := Algebra.TensorProduct.leftAlgebra
      letI : Algebra C₀ Tprefix := Algebra.TensorProduct.rightAlgebra
      let fT := completedFiniteModelTowerAlgHom
        (R := B) (R' := Bhat) (S₀ := C₀) (S₁ := E) g
      let Nprefix := Nfinal.comap fT.toRingHom
      let hNprefixPrime : Nprefix.IsPrime :=
        hNfinalPrime.comap fT.toRingHom
      letI : Nprefix.IsPrime := hNprefixPrime
      let hNprefixOver : Nprefix.LiesOver (⊥ : Ideal Bhat) := by
        refine ⟨?_⟩
        ext x
        change x ∈ (⊥ : Ideal Bhat) ↔
          fT (algebraMap Bhat Tprefix x) ∈ Nfinal
        rw [fT.commutes x]
        exact Nfinal.mem_of_liesOver (⊥ : Ideal Bhat) x
      letI : Nprefix.LiesOver (⊥ : Ideal Bhat) := hNprefixOver
      let mPrefix := retainedCompletedGenericTensorIdeal
        (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
        (K' := Khat) Nprefix
      let hmPrefix : mPrefix.IsMaximal :=
        retainedCompletedGenericTensorIdeal_isMaximal
          (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
          (K' := Khat) Nprefix
      letI : mPrefix.IsMaximal := hmPrefix
      let OmegaPrefix := GenericTensorFieldComponent mPrefix
      let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
        genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
      letI : Algebra Bhat OmegaPrefix := bHatOmegaPrefixAlgebra
      let ICprefix := selectedPrefixNormalizationRing
        (B := B) (KB := KB) (M₀ := M₀)
        yB zB hregB hgenB Nprefix
      let prefixOwner := selectedPrefixNormalizationOwner
        (B := B) (KB := KB) (M₀ := M₀)
        yB zB hregB hgenB Nprefix
      letI : CommRing ICprefix := prefixOwner.commRingΩ
      letI : Algebra Bhat ICprefix := prefixOwner.algebra
      ∃ qhatPrefix : Ideal ICprefix,
        ∃ hqhatPrime : qhatPrefix.IsPrime,
          ∃ hqhatOver : qhatPrefix.LiesOver
              (Ideal.span ({yhat} : Set Bhat)),
            letI : qhatPrefix.IsPrime := hqhatPrime
            letI : qhatPrefix.LiesOver
                (Ideal.span ({yhat} : Set Bhat)) := hqhatOver
            qhatPrefix.ramificationIdx Bhat = N ∧
              (Localization.awayMap
                (algebraMap Bhat ICprefix)
                yhat).Etale

private inductive SelectedExponentPrefixPackage
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [Algebra B (integralClosure D M)]
    (yB zB : B)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (N : ℕ)
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (p : Ideal (integralClosure D M)) : Prop where
  | mk :
      SelectedExponentPrefixPackageBody
        (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
        yB zB hregB hgenB N g p →
      SelectedExponentPrefixPackage yB zB hregB hgenB N g p

/-- Complete the selected-branch argument from the explicit finite models and
the retained source primes.  The global-source construction owns the models;
this core starts with a fresh instance context. -/
private theorem selectedExponent_completion_prefix
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀] [FiniteDimensional KB M₀]
    [Algebra.IsSeparable KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [FaithfulSMul B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [IsIntegrallyClosed (integralClosure B M₀)]
    [Algebra B (integralClosure D M)]
    [Module.Flat B (integralClosure D M)]
    (yB zB : B) (N : ℕ)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (qGlobal p : Ideal (integralClosure D M))
    (hqGlobalPrime : qGlobal.IsPrime)
    (hqGlobalOverB : qGlobal.LiesOver (Ideal.span ({yB} : Set B)))
    (hqGlobalLe : qGlobal ≤ p)
    (hpMax : p.IsMaximal)
    (hpOverB : p.LiesOver (maximalIdeal B))
    (qPrefix : Ideal (integralClosure B M₀))
    [hqPrefixPrime : qPrefix.IsPrime]
    [hqPrefixOverB : qPrefix.LiesOver (Ideal.span ({yB} : Set B))]
    (hqGlobalComap : qGlobal.comap g.toRingHom = qPrefix)
    (hqPrefixExact : qPrefix.ramificationIdx B = N)
    (hAwayPrefix :
      (Localization.awayMap
        (algebraMap B (integralClosure B M₀)) yB).Etale) :
    SelectedExponentPrefixPackage
      (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
      yB zB hregB hgenB N g p := by
  classical
  let C₀ := integralClosure B M₀
  let E := integralClosure D M
  have hCompletedChain :=
    selectedExponent_completed_prime_chain_source
      (B := B) (E := E)
      yB zB hregB hgenB qGlobal p
      hqGlobalPrime hqGlobalOverB hqGlobalLe hpMax hpOverB
  unfold SelectedCompletedPrimeChainPackage at hCompletedChain
  obtain
      ⟨Nfinal, Qfinal, hNfinalQfinal, hNfinalLePfinal,
        hNfinalPrime, hNfinalComap, hQfinalPrime, hQfinalComap,
        hQfinalBranchComap, hPfinalMax⟩ :=
    hCompletedChain
  let qB := Ideal.span ({yB} : Set B)
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  have hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  let : IsDomain Bhat := hgeometryHat.1
  have hBhatNoetherian : IsNoetherianRing Bhat :=
    maximalAdicCompletion_isNoetherianRing_of_regularPair hregB hgenB
  let Tfinal := Bhat ⊗[B] E
  let : Algebra Bhat Tfinal := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Tfinal := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B Bhat Tfinal :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower B E Tfinal :=
    Algebra.TensorProduct.right_isScalarTower
  let Pfinal := p.map
    (Algebra.TensorProduct.includeRight
      (R := B) (A := Bhat) (B := E)).toRingHom
  have hNfinalOver : Nfinal.LiesOver (⊥ : Ideal Bhat) :=
    (Ideal.liesOver_iff Nfinal (⊥ : Ideal Bhat)).mpr
      hNfinalComap.symm
  have hQfinalBranch :
      Qfinal.LiesOver (Ideal.span ({yhat} : Set Bhat)) :=
    (Ideal.liesOver_iff Qfinal
      (Ideal.span ({yhat} : Set Bhat))).mpr hQfinalBranchComap.symm
  let Tprefix := Bhat ⊗[B] C₀
  let : Algebra Bhat Tprefix := Algebra.TensorProduct.leftAlgebra
  let : Algebra C₀ Tprefix := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B Bhat Tprefix :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower B C₀ Tprefix :=
    Algebra.TensorProduct.right_isScalarTower
  let fT := completedFiniteModelTowerAlgHom
    (R := B) (R' := Bhat) (S₀ := C₀) (S₁ := E) g
  let Nprefix := Nfinal.comap fT.toRingHom
  let Qprefix := Qfinal.comap fT.toRingHom
  obtain
      ⟨hNprefixQprefix, hNprefixPrime, hNprefixOver,
        hQprefixPrime, hQprefixBranch,
        hQprefixRight, hQprefixExact⟩ :=
    selectedExponent_contracted_prefix_source
      (R := B) (R' := Bhat) (S₀ := C₀) (S₁ := E)
      (_hq₁Prime := hqGlobalPrime)
      (_hNPrime := hNfinalPrime) (_hNOver := hNfinalOver)
      (_hQPrime := hQfinalPrime) (hQBranch := hQfinalBranch)
      (hCharZero := hCharB)
      yB qPrefix g qGlobal hqGlobalComap Nfinal Qfinal
      hQfinalComap hNfinalQfinal hqPrefixExact
  have hyBHeight : qB.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hyBPrime.ne_zero)
      hyBPrime.not_isUnit
  let : Algebra.IsIntegral B C₀ := Algebra.IsIntegral.of_finite B C₀
  let : IsNoetherianRing C₀ := IsNoetherianRing.of_finite B C₀
  let : IsIntegrallyClosed B :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdimB
  have hqPrefixHeight : qPrefix.height = 1 := by
    calc
      qPrefix.height = (qPrefix.under B).height :=
        SpecialLocalPurity.height_eq_height_under_of_faithfully_integral_over_integrallyClosed
          qPrefix
      _ = qB.height := by
        simpa only [qB] using
          (congrArg Ideal.height hqPrefixOverB.over).symm
      _ = 1 := hyBHeight
  obtain ⟨hWprefixDomain, hWprefixDVR⟩ :=
    selectedExponent_prefix_localization_dvr
      (R := B) (S := C₀) (R' := Bhat)
      (hR'Noetherian := hBhatNoetherian)
      (hQPrime := hQprefixPrime) (_hQBranch := hQprefixBranch)
      (hCharZero := hCharB)
      yB qPrefix Qprefix hQprefixRight hqPrefixHeight
  let Khat := FractionRing Bhat
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  let : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  let : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let mPrefix := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
    (K' := Khat) Nprefix
  let : mPrefix.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) (hNPrime := hNprefixPrime)
      (hNOver := hNprefixOver) Nprefix
  let OmegaPrefix := GenericTensorFieldComponent mPrefix
  let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
  let : SMul Bhat OmegaPrefix := bHatOmegaPrefixAlgebra.toSMul
  let : IsScalarTower Bhat Khat OmegaPrefix :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ICprefix := selectedPrefixNormalizationRing
    (B := B) (KB := KB) (M₀ := M₀)
    (hNprefixPrime := hNprefixPrime)
    (hNprefixOver := hNprefixOver)
    yB zB hregB hgenB Nprefix
  let prefixOwner := selectedPrefixNormalizationOwner
    (B := B) (KB := KB) (M₀ := M₀)
    (hNprefixPrime := hNprefixPrime)
    (hNprefixOver := hNprefixOver)
    yB zB hregB hgenB Nprefix
  let : CommRing ICprefix := prefixOwner.commRingΩ
  let : Algebra Bhat ICprefix := prefixOwner.algebra
  obtain ⟨hprefixNormalization⟩ :=
    selectedExponent_prefix_normalization_source
      (B := B) (KB := KB) (M₀ := M₀)
      (_hNprefixPrime := hNprefixPrime)
      (_hNprefixOver := hNprefixOver)
      (_hQprefixPrime := hQprefixPrime)
      (hQprefixBranch := hQprefixBranch)
      (_hWprefixDomain := hWprefixDomain)
      (_hWprefixDVR := hWprefixDVR)
      yB zB hregB hgenB hdimB N Nprefix Qprefix
      hNprefixQprefix hQprefixExact hAwayPrefix
  obtain
      ⟨qhatPrefix, hqhatPrefixPrime, hqhatPrefixOverBranch,
        hqhatPrefixExact, hAwayPrefixHat⟩ := hprefixNormalization
  apply SelectedExponentPrefixPackage.mk
  unfold SelectedExponentPrefixPackageBody
  dsimp only
  refine ⟨Nfinal, hNfinalPrime, hNfinalOver,
    hNfinalLePfinal, hPfinalMax,
    qhatPrefix, hqhatPrefixPrime, hqhatPrefixOverBranch, ?_⟩
  exact ⟨hqhatPrefixExact, hAwayPrefixHat⟩


/-- In a finite algebra over a local ring, a prime above the closed point is
the unique maximal ideal of the local target. -/
private theorem prime_eq_maximalIdeal_of_liesOver_of_finite
    {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S] [Module.Finite R S]
    (Q : Ideal S) (hQPrime : Q.IsPrime)
    (hQOver : Q.LiesOver (maximalIdeal R)) :
    Q = maximalIdeal S := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hQMaximal : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap R S)
      (algebraMap_isIntegral_iff.mpr
        (inferInstance : Algebra.IsIntegral R S)) Q <| by
        rw [← Ideal.under_def, ← Q.over_def (maximalIdeal R)]
        exact maximalIdeal.isMaximal R
  exact IsLocalRing.eq_maximalIdeal hQMaximal


/-- The integral closure inside a field extension is faithful over the base
domain through the chosen fraction field. -/
private theorem integralClosure_faithfulSMul_of_fractionField
    {R K L : Type u}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L] :
    FaithfulSMul R (integralClosure R L) := by
  apply (faithfulSMul_iff_algebraMap_injective
    R (integralClosure R L)).mpr
  intro x z hxz
  apply IsFractionRing.injective R K
  apply (algebraMap K L).injective
  have hxL := congrArg (fun c : integralClosure R L ↦ (c : L)) hxz
  change algebraMap R L x = algebraMap R L z at hxL
  calc
    algebraMap K L (algebraMap R K x) = algebraMap R L x :=
      (IsScalarTower.algebraMap_apply R K L x).symm
    _ = algebraMap R L z := hxL
    _ = algebraMap K L (algebraMap R K z) :=
      IsScalarTower.algebraMap_apply R K L z


/-- Compatibility around a square of algebra towers. -/
private theorem isScalarTower_of_algebra_tower_square
    {R S T U : Type u}
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra R T] [Algebra S T]
    [Algebra R U] [Algebra S U] [Algebra T U]
    [IsScalarTower R S T] [IsScalarTower R T U]
    [IsScalarTower S T U] :
    IsScalarTower R S U := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  calc
    algebraMap R U x = algebraMap T U (algebraMap R T x) :=
      IsScalarTower.algebraMap_apply R T U x
    _ = algebraMap T U (algebraMap S T (algebraMap R S x)) := by
      rw [← IsScalarTower.algebraMap_apply R S T]
    _ = algebraMap S U (algebraMap R S x) :=
      (IsScalarTower.algebraMap_apply S T U _).symm


/-- The algebra structures transported through the completed root pushout
form the expected base tower. -/
private theorem tensorPushoutEquiv_base_isScalarTower
    {B D Bhat Broot : Type u}
    [CommRing B] [CommRing D] [CommRing Bhat] [CommRing Broot]
    [Algebra B D] [Algebra B Bhat] [Algebra Bhat Broot]
    (e : (Bhat ⊗[B] D) ≃ₐ[Bhat] Broot) :
    let dBrootAlgebra : Algebra D Broot :=
      (e.toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
    let bBrootAlgebra : Algebra B Broot :=
      ((algebraMap Bhat Broot).comp (algebraMap B Bhat)).toAlgebra
    @IsScalarTower B D Broot
      (inferInstance : Algebra B D).toSMul
      dBrootAlgebra.toSMul bBrootAlgebra.toSMul := by
  let dBrootAlgebra : Algebra D Broot :=
    (e.toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom).toAlgebra
  let bBrootAlgebra : Algebra B Broot :=
    ((algebraMap Bhat Broot).comp (algebraMap B Bhat)).toAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro x
  calc
    algebraMap B Broot x =
        e (algebraMap Bhat (Bhat ⊗[B] D) (algebraMap B Bhat x)) :=
      (e.commutes (algebraMap B Bhat x)).symm
    _ = e (Algebra.TensorProduct.includeRight (algebraMap B D x)) := by
      congr 1
      exact DFunLike.congr_fun
        Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x
    _ = algebraMap D Broot (algebraMap B D x) := rfl


/-- Package the retained final component map uniformly in the later domain
instance.  Its construction is checked outside the selected-branch context. -/
private theorem exists_retainedCompletedComponentToChosenLocalFractionAlgHom
    {R R' S K L K' : Type u}
    [CommRing R] [IsDomain R]
    [CommRing R'] [IsDomain R'] [Algebra R R']
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    [Algebra R K'] [IsScalarTower R R' K']
    [Algebra K K'] [IsScalarTower R K K']
    (N P : Ideal (R' ⊗[R] S)) [N.IsPrime]
    [N.LiesOver (⊥ : Ideal R')]
    (hNP : N ≤ P) (hPMax : P.IsMaximal) :
    let m := retainedCompletedGenericTensorIdeal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    letI : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
      (R := R) (R' := R') (S := S) (K := K) (L := L)
      (K' := K') N
    let Omega := GenericTensorFieldComponent m
    letI : Algebra R' Omega :=
      genericTensorFieldComponentLeftScalarAlgebra (R := R') m
    ∃ _f : ∀ [IsDomain (Localization.AtPrime P)],
        Omega →ₐ[R'] FractionRing (Localization.AtPrime P),
      True := by
  classical
  dsimp only
  let m := retainedCompletedGenericTensorIdeal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let : m.IsMaximal := retainedCompletedGenericTensorIdeal_isMaximal
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N
  let Omega := GenericTensorFieldComponent m
  let r'OmegaAlgebra : Algebra R' Omega :=
    genericTensorFieldComponentLeftScalarAlgebra (R := R') m
  let : P.IsPrime := hPMax.isPrime
  refine ⟨?_, True.intro⟩
  intro _hDomain
  exact (retainedCompletedComponentToChosenLocalFractionAlgEquiv
    (R := R) (R' := R') (S := S) (K := K) (L := L)
    (K' := K') N P hNP).toAlgHom


/-- Close the argument once the finite-etale local factor and its unique
closed prime have been constructed. -/
private theorem selectedExponent_finish_local_factor
    {A Omega OmegaFinal : Type u}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field Omega] [Algebra A Omega] [Algebra (FractionRing A) Omega]
    [IsScalarTower A (FractionRing A) Omega]
    [FiniteDimensional (FractionRing A) Omega]
    [IsGalois (FractionRing A) Omega]
    [Field OmegaFinal] [Algebra A OmegaFinal]
    [Algebra (FractionRing A) OmegaFinal]
    [IsScalarTower A (FractionRing A) OmegaFinal]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hChar : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    (fTower : Omega →ₐ[FractionRing A] OmegaFinal)
    (q : Ideal (integralClosure A Omega))
    (hqPrime : q.IsPrime)
    (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
    (hqExact : q.ramificationIdx A = N)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) y).Etale) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let Broot := iteratedRadical A 1 n a
    let hymax : y ∈ maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    let ha : ∀ i, a i ∈ maximalIdeal A := fun _ ↦ hymax
    letI : IsLocalRing Broot :=
      isLocalRing_iteratedRadical n a (fun _ ↦ hN) ha
    ∀ {Dlocal : Type u} [CommRing Dlocal] [IsLocalRing Dlocal]
      [Algebra A Dlocal] [Algebra Broot Dlocal]
      [IsScalarTower A Broot Dlocal]
      [Module.Finite Broot Dlocal] [Algebra.Etale Broot Dlocal]
      [IsLocalHom (algebraMap Broot Dlocal)] [FaithfulSMul A Dlocal],
      ∀ (qD : Ideal Dlocal) [qD.IsPrime]
        [qD.LiesOver (maximalIdeal Broot)],
        (∀ Q : Ideal Dlocal, Q.IsPrime →
          Q.LiesOver (maximalIdeal Broot) → Q = qD) →
        (∀ [IsDomain Dlocal],
          OmegaFinal →ₐ[A] FractionRing Dlocal) →
        IsUnit (N : A) := by
  classical
  dsimp only
  intro Dlocal _ _ _ _ _ _ _ _ _ qD hqDPrime hqDOver
    huniqueD fFinal
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let Broot := iteratedRadical A 1 n a
  have hymax : y ∈ maximalIdeal A := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have ha : ∀ i, a i ∈ maximalIdeal A := fun _ ↦ hymax
  let : IsLocalRing Broot :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) ha
  have hdimAux :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [y, z] hreg
  rw [hgen] at hdimAux
  let : Field (A ⧸ maximalIdeal A) :=
    Ideal.Quotient.field (maximalIdeal A)
  have hfieldDim : ringKrullDim (A ⧸ maximalIdeal A) = 0 :=
    ringKrullDim_eq_zero_of_field _
  rw [hfieldDim, zero_add] at hdimAux
  have hdim : ringKrullDim A = ((2 : ℕ∞) : WithBot ℕ∞) := by
    norm_num [List.length_cons, List.length_nil] at hdimAux
    exact hdimAux.symm
  let : Module.Finite A (integralClosure A Omega) :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := FractionRing A) hdim
  obtain ⟨eResidueTensor, hTerminal⟩ :=
    exists_completeRegularPairChosenFactor_oneRoot_exponent_isUnit_of_exactNormalizationPrime
      (A := A) y z hreg hgen N hN hChar
      (D := Dlocal) qD huniqueD
  let l := ResidueField Dlocal
  let : Module.Finite A Broot :=
    finite_iteratedRadical n a (fun _ ↦ hN)
  let : Module.FaithfullyFlat A Broot :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : Algebra.IsIntegral A Broot :=
    Algebra.IsIntegral.of_finite A Broot
  let : IsLocalHom (algebraMap A Broot) :=
    Algebra.IsIntegral.isLocalHom A Broot
  let : IsLocalHom (algebraMap A Dlocal) := by
    rw [IsScalarTower.algebraMap_eq A Broot Dlocal]
    infer_instance
  let k := ResidueField A
  let kRoot := ResidueField Broot
  let eResidue : k ≃ₐ[k] kRoot :=
    AlgEquiv.ofBijective (Algebra.ofId k kRoot)
      (residueFieldMap_bijective_iteratedRadical
        n a (fun _ ↦ hN) ha)
  let : Module.Finite k kRoot :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kRoot l
  let : Algebra.IsSeparable k kRoot :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l :=
    Algebra.IsSeparable.trans k kRoot l
  let C₁ := FiniteEtaleResidueLift A l
  let : IsLocalRing C₁ := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C₁ := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C₁ := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.Etale A C₁ := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C₁ := Algebra.IsIntegral.of_finite A C₁
  let : IsLocalHom (algebraMap A C₁) :=
    Algebra.IsIntegral.isLocalHom A C₁
  let : Module.FaithfullyFlat A C₁ :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : IsDomain C₁ :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  let : Algebra C₁ Dlocal :=
    tensorChosenFactorRightAlgebra eResidueTensor
  let : IsScalarTower A C₁ Dlocal := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A Dlocal x =
          algebraMap Broot Dlocal (algebraMap A Broot x) :=
        IsScalarTower.algebraMap_apply A Broot Dlocal x
      _ = eResidueTensor
          (algebraMap Broot (Broot ⊗[A] C₁)
            (algebraMap A Broot x)) :=
        (eResidueTensor.commutes (algebraMap A Broot x)).symm
      _ = eResidueTensor
          (Algebra.TensorProduct.includeRight (algebraMap A C₁ x)) := by
        congr 1
        exact DFunLike.congr_fun
          Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x
      _ = algebraMap C₁ Dlocal (algebraMap A C₁ x) := rfl
  let yC := algebraMap A C₁ y
  let Rn := AdjoinRoot (X ^ N - Polynomial.C yC)
  let eRoot : Rn ≃ₐ[C₁] Dlocal :=
    oneRootChosenFactorAlgEquiv N y eResidueTensor
  let : IsDomain Rn := by
    simpa only [Rn, C₁, yC] using
      (finiteEtaleResidueLift_pair_adjoinRoot_isDomain_of_regularPair
        (l := l) y z hreg hgen N hN)
  let : IsDomain Dlocal := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C₁ Rn :=
    (monic_X_pow_sub_C yC hN.ne').free_adjoinRoot
  let : FaithfulSMul C₁ Rn := Module.FaithfullyFlat.faithfulSMul
  let Pfield := FractionRing Dlocal
  let : IsScalarTower A Dlocal Pfield :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FaithfulSMul A Pfield := FaithfulSMul.trans A Dlocal Pfield
  let : Algebra (FractionRing A) Pfield :=
    FractionRing.liftAlgebra A Pfield
  let : IsScalarTower A (FractionRing A) Pfield :=
    FractionRing.isScalarTower_liftAlgebra A Pfield
  let eFinalA : OmegaFinal →ₐ[A] Pfield := fFinal
  let eFinalF : OmegaFinal →ₐ[FractionRing A] Pfield :=
    fractionFieldBaseAlgHomOfRestrictScalars
      (A := A) (F := FractionRing A) eFinalA
  let fPrefix : Omega →ₐ[FractionRing A] Pfield :=
    eFinalF.comp fTower
  let cPAlgebra : Algebra C₁ Pfield :=
    fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : SMul C₁ Pfield := cPAlgebra.toSMul
  let : @FaithfulSMul C₁ Pfield cPAlgebra.toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      C₁ Pfield _ _ cPAlgebra).mpr
    have hCDlocal : Function.Injective (algebraMap C₁ Dlocal) := by
      intro x x' hxx'
      apply FaithfulSMul.algebraMap_injective C₁ Rn
      apply eRoot.injective
      simpa only [eRoot.commutes] using hxx'
    change Function.Injective
      ((algebraMap Dlocal Pfield).comp (algebraMap C₁ Dlocal))
    exact (IsFractionRing.injective Dlocal Pfield).comp hCDlocal
  let : @IsScalarTower C₁ Dlocal Pfield
      (inferInstance : Algebra C₁ Dlocal).toSMul
      (inferInstance : Algebra Dlocal Pfield).toSMul
      cPAlgebra.toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @IsScalarTower A C₁ Pfield
      (inferInstance : Algebra A C₁).toSMul
      cPAlgebra.toSMul
      (inferInstance : Algebra A Pfield).toSMul :=
    isScalarTower_of_algebra_tower_square
      (R := A) (S := C₁) (T := Dlocal) (U := Pfield)
  let KC := FractionRing C₁
  let kcPAlgebra : Algebra KC Pfield := fractionRingAlgebraOfAlgEquiv eRoot
  let : SMul KC Pfield := kcPAlgebra.toSMul
  let : @IsScalarTower C₁ KC Pfield
      (inferInstance : Algebra C₁ KC).toSMul
      kcPAlgebra.toSMul cPAlgebra.toSMul :=
    FractionRing.isScalarTower_liftAlgebra C₁ Pfield
  let aKCAlgebra : Algebra A KC :=
    ((algebraMap C₁ KC).comp (algebraMap A C₁)).toAlgebra
  let : SMul A KC := aKCAlgebra.toSMul
  let : @IsScalarTower A C₁ KC
      (inferInstance : Algebra A C₁).toSMul
      (inferInstance : Algebra C₁ KC).toSMul
      aKCAlgebra.toSMul := IsScalarTower.of_algebraMap_eq' rfl
  let : @FaithfulSMul A KC aKCAlgebra.toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective A KC _ _ aKCAlgebra).mpr
    change Function.Injective
      ((algebraMap C₁ KC).comp (algebraMap A C₁))
    exact (IsFractionRing.injective C₁ KC).comp
      (FaithfulSMul.algebraMap_injective A C₁)
  let : Algebra (FractionRing A) KC := FractionRing.liftAlgebra A KC
  let : IsScalarTower A (FractionRing A) KC :=
    FractionRing.isScalarTower_liftAlgebra A KC
  exact prefixEmbedding_exactPrimeBoundaryAway_terminal_isUnit
    (A := A) (C := C₁) (F := FractionRing A) (KC := KC)
    (M := Omega) (P := Pfield)
    y z hreg hgen hdim N fPrefix q hqPrime hqOver hqExact hAway hTerminal


/-- Finish the selected-exponent argument from the completed one-root factor.
The retained construction supplies only the final component map; all local
factor and residue-lift instances are confined to this declaration. -/
private theorem selectedExponent_finish_after_final_root
    {A Omega OmegaFinal : Type u}
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field Omega] [Algebra A Omega] [Algebra (FractionRing A) Omega]
    [IsScalarTower A (FractionRing A) Omega]
    [FiniteDimensional (FractionRing A) Omega]
    [IsGalois (FractionRing A) Omega]
    [Field OmegaFinal] [Algebra A OmegaFinal]
    [Algebra (FractionRing A) OmegaFinal]
    [IsScalarTower A (FractionRing A) OmegaFinal]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hChar : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    (fTower : Omega →ₐ[FractionRing A] OmegaFinal)
    (q : Ideal (integralClosure A Omega))
    (hqPrime : q.IsPrime)
    (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
    (hqExact : q.ramificationIdx A = N)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) y).Etale) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    let Broot := iteratedRadical A 1 n a
    let hymax : y ∈ maximalIdeal A := by
      rw [← hgen]
      exact Ideal.subset_span (by simp)
    let ha : ∀ i, a i ∈ maximalIdeal A := fun _ ↦ hymax
    letI : IsLocalRing Broot :=
      isLocalRing_iteratedRadical n a (fun _ ↦ hN) ha
    ∀ {T : Type u} [CommRing T] [Algebra A T] [Algebra Broot T]
      [IsScalarTower A Broot T] [Module.Finite Broot T]
      [Algebra.Etale Broot T],
      ∀ (P : Ideal T) [P.IsMaximal]
        [P.LiesOver (maximalIdeal Broot)],
        (∀ [IsDomain (Localization.AtPrime P)],
          OmegaFinal →ₐ[A] FractionRing (Localization.AtPrime P)) →
          IsUnit (N : A) := by
  classical
  dsimp only
  intro T _ _ _ _ _ _ P hPMax hPOver fFinal
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ y
  let Broot := iteratedRadical A 1 n a
  have hymax : y ∈ maximalIdeal A := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  have ha : ∀ i, a i ∈ maximalIdeal A := fun _ ↦ hymax
  let : IsLocalRing Broot :=
    isLocalRing_iteratedRadical n a (fun _ ↦ hN) ha
  let : HenselianLocalRing Broot :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete
      n a (fun _ ↦ hN) ha
  let : P.IsPrime := hPMax.isPrime
  let Dp := Localization.AtPrime P
  let : Algebra T Dp := inferInstance
  let bRootDpAlgebra : Algebra Broot Dp := inferInstance
  let : SMul Broot Dp := bRootDpAlgebra.toSMul
  let : IsScalarTower Broot T Dp := inferInstance
  let : Module.Finite Broot Dp :=
    moduleFinite_localizationAtPrime_of_henselian_of_etale P
  let : Algebra.Etale Broot Dp :=
    etale_localizationAtPrime_of_henselian_of_etale P
  let : IsLocalHom (algebraMap Broot Dp) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal P
  have huniqueDp : ∀ Q : Ideal Dp, Q.IsPrime →
      Q.LiesOver (maximalIdeal Broot) → Q = maximalIdeal Dp := by
    intro Q hQPrime hQOver
    exact prime_eq_maximalIdeal_of_liesOver_of_finite
      (R := Broot) (S := Dp) Q hQPrime hQOver
  let aDpAlgebra : Algebra A Dp := inferInstance
  let : SMul A Dp := aDpAlgebra.toSMul
  let : IsScalarTower A Broot Dp :=
    isScalarTower_of_algebra_tower_square
      (R := A) (S := Broot) (T := T) (U := Dp)
  let : Module.FaithfullyFlat A Broot :=
    faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
  let : @Module.FaithfullyFlat Broot Dp _ _
      bRootDpAlgebra.toModule :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom
      Broot Dp _ _ bRootDpAlgebra _ _ _ _
  let : @FaithfulSMul A Dp aDpAlgebra.toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      A Dp _ _ aDpAlgebra).mpr
    intro x x' hxx'
    apply FaithfulSMul.algebraMap_injective A Broot
    apply FaithfulSMul.algebraMap_injective Broot Dp
    simpa only [IsScalarTower.algebraMap_apply A Broot Dp] using hxx'
  let qDp := maximalIdeal Dp
  let : qDp.IsPrime := (maximalIdeal.isMaximal Dp).isPrime
  let : qDp.LiesOver (maximalIdeal Broot) := by
    apply (Ideal.liesOver_iff _ _).mpr
    exact (IsLocalRing.maximalIdeal_comap (algebraMap Broot Dp)).symm
  exact selectedExponent_finish_local_factor
    (A := A) (Omega := Omega) (OmegaFinal := OmegaFinal)
    y z hreg hgen N hN hChar fTower q hqPrime hqOver hqExact hAway
    (Dlocal := Dp) qDp huniqueDp fFinal


/-- Transport the finite-etale model across the completed one-root pushout,
then hand the resulting local factor to the terminal calculation. -/
private theorem selectedExponent_finish_completed_root_pushout
    {B D E A Omega OmegaFinal : Type u}
    [CommRing B]
    [CommRing D] [Algebra B D]
    [CommRing E] [Algebra B E] [Algebra D E]
    [IsScalarTower B D E] [Module.Finite D E] [Algebra.Etale D E]
    [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra B A]
    [Field Omega] [Algebra A Omega] [Algebra (FractionRing A) Omega]
    [IsScalarTower A (FractionRing A) Omega]
    [FiniteDimensional (FractionRing A) Omega]
    [IsGalois (FractionRing A) Omega]
    [Field OmegaFinal] [Algebra A OmegaFinal]
    [Algebra (FractionRing A) OmegaFinal]
    [IsScalarTower A (FractionRing A) OmegaFinal]
    (y z : A)
    (hreg : IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal A)
    (N : ℕ) (hN : 0 < N)
    (hyMax : y ∈ maximalIdeal A)
    (hChar : CharZero (A ⧸ Ideal.span ({y} : Set A)))
    (eBaseRoot :
      (A ⊗[B] D) ≃ₐ[A] AdjoinRoot (X ^ N - Polynomial.C y))
    (Pfinal : Ideal (A ⊗[B] E))
    (hPfinalMax : Pfinal.IsMaximal)
    (fFinal :
      ∀ [IsDomain (Localization.AtPrime Pfinal)],
        OmegaFinal →ₐ[A] FractionRing (Localization.AtPrime Pfinal))
    (fTower : Omega →ₐ[FractionRing A] OmegaFinal)
    (q : Ideal (integralClosure A Omega))
    (hqPrime : q.IsPrime)
    (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
    (hqExact : q.ramificationIdx A = N)
    (hAway :
      (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) y).Etale) :
    IsUnit (N : A) := by
  classical
  let nOne : Fin 1 → ℕ := fun _ ↦ N
  let aHat : Fin 1 → A := fun _ ↦ y
  let Broot := iteratedRadical A 1 nOne aHat
  let haHat : ∀ i, aHat i ∈ maximalIdeal A := fun _ ↦ hyMax
  let : IsLocalRing Broot :=
    isLocalRing_iteratedRadical nOne aHat (fun _ ↦ hN) haHat
  let tensorRoot := A ⊗[B] D
  let : Algebra A tensorRoot := Algebra.TensorProduct.leftAlgebra
  let : Algebra D tensorRoot := Algebra.TensorProduct.rightAlgebra
  let rootA := AdjoinRoot (X ^ N - Polynomial.C y)
  let eBaseRootTensor : tensorRoot ≃ₐ[A] rootA := by
    simpa only [tensorRoot, rootA] using eBaseRoot
  let eOne : Broot ≃ₐ[A] rootA := by
    simpa only [Broot, nOne, aHat] using
      (oneIteratedRadicalAlgEquiv A N y)
  let ePush : tensorRoot ≃ₐ[A] Broot :=
    eBaseRootTensor.trans eOne.symm
  let dBrootAlgebra : Algebra D Broot :=
    (ePush.toRingHom.comp (algebraMap D tensorRoot)).toAlgebra
  let bBrootAlgebra : Algebra B Broot :=
    ((algebraMap A Broot).comp (algebraMap B A)).toAlgebra
  let : IsScalarTower B A Broot := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B D Broot :=
    tensorPushoutEquiv_base_isScalarTower ePush
  let ePushD : tensorRoot ≃ₐ[D] Broot :=
    AlgEquiv.ofRingEquiv (f := ePush.toRingEquiv) (fun _ ↦ rfl)
  let : Algebra.IsPushout B D A Broot := by
    apply Algebra.IsPushout.of_equiv ePushD
    ext x
    exact ePush.commutes x
  let : Algebra.IsPushout B A D Broot :=
    Algebra.IsPushout.symm
      (inferInstance : Algebra.IsPushout B D A Broot)
  let Tfinal := A ⊗[B] E
  let : Algebra A Tfinal := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Tfinal := Algebra.TensorProduct.rightAlgebra
  let Ehat := Broot ⊗[D] E
  let : Algebra Broot Ehat := Algebra.TensorProduct.leftAlgebra
  let eTensorA : Ehat ≃ₐ[A] Tfinal :=
    Algebra.IsPushout.cancelBaseChangeAlg B A D Broot E
  let bRootTfinalAlgebra : Algebra Broot Tfinal :=
    (eTensorA.toRingHom.comp (algebraMap Broot Ehat)).toAlgebra
  let eTensor : Ehat ≃ₐ[Broot] Tfinal :=
    AlgEquiv.ofRingEquiv (f := eTensorA.toRingEquiv) (fun _ ↦ rfl)
  let : IsScalarTower A Broot Tfinal := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A Tfinal x = eTensorA (algebraMap A Ehat x)
    exact (eTensorA.commutes x).symm
  let : Module.Finite Broot Ehat := inferInstance
  let : Algebra.Etale Broot Ehat := inferInstance
  let : Module.Finite Broot Tfinal :=
    Module.Finite.of_surjective eTensor.toLinearMap eTensor.surjective
  let : Algebra.Etale Broot Tfinal := Algebra.Etale.of_equiv eTensor
  let : Algebra.IsIntegral Broot Tfinal :=
    Algebra.IsIntegral.of_finite Broot Tfinal
  let : Pfinal.IsPrime := hPfinalMax.isPrime
  have hPfinalOverRoot : Pfinal.LiesOver (maximalIdeal Broot) := by
    have hUnderMax : (Pfinal.under Broot).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
        (algebraMap Broot Tfinal) (fun x ↦ Algebra.IsIntegral.isIntegral x)
        Pfinal
    exact ⟨(IsLocalRing.eq_maximalIdeal hUnderMax).symm⟩
  let : HenselianLocalRing Broot :=
    henselianLocalRing_iteratedRadical_of_isAdicComplete
      nOne aHat (fun _ ↦ hN) haHat
  exact selectedExponent_finish_after_final_root
    (A := A) (Omega := Omega) (OmegaFinal := OmegaFinal)
    y z hreg hgen N hN hChar fTower q hqPrime hqOver hqExact hAway
    (T := Tfinal) Pfinal fFinal


/- The minimal typed boundary between retained-component selection and the
completed one-root terminal. -/
private inductive SelectedExponentRootReadyPackage
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    (N : ℕ) : Prop where
  | mk
      (E A Omega OmegaFinal : Type u)
      [CommRing E] [Algebra B E] [Algebra D E]
      [IsScalarTower B D E] [Module.Finite D E] [Algebra.Etale D E]
      [CommRing A] [IsDomain A] [IsRegularLocalRing A]
      [IsAdicComplete (maximalIdeal A) A] [Algebra B A]
      [Field Omega] [Algebra A Omega] [Algebra (FractionRing A) Omega]
      [IsScalarTower A (FractionRing A) Omega]
      [FiniteDimensional (FractionRing A) Omega]
      [IsGalois (FractionRing A) Omega]
      [Field OmegaFinal] [Algebra A OmegaFinal]
      [Algebra (FractionRing A) OmegaFinal]
      [IsScalarTower A (FractionRing A) OmegaFinal]
      (y z : A)
      (hreg : IsRegular A [y, z])
      (hgen : Ideal.ofList [y, z] = maximalIdeal A)
      (hN : 0 < N)
      (hyMax : y ∈ maximalIdeal A)
      (hChar : CharZero (A ⧸ Ideal.span ({y} : Set A)))
      (eBaseRoot : (A ⊗[B] D) ≃ₐ[A]
        AdjoinRoot (X ^ N - Polynomial.C y))
      (Pfinal : Ideal (A ⊗[B] E))
      (hPfinalMax : Pfinal.IsMaximal)
      (fFinal : ∀ [IsDomain (Localization.AtPrime Pfinal)],
        OmegaFinal →ₐ[A] FractionRing (Localization.AtPrime Pfinal))
      (fTower : Omega →ₐ[FractionRing A] OmegaFinal)
      (q : Ideal (integralClosure A Omega))
      (hqPrime : q.IsPrime)
      (hqOver : q.LiesOver (Ideal.span ({y} : Set A)))
      (hqExact : q.ramificationIdx A = N)
      (hAway : (Localization.awayMap
        (algebraMap A (integralClosure A Omega)) y).Etale)
      (reflectUnit : IsUnit (N : A) → IsUnit (N : B)) :
      SelectedExponentRootReadyPackage N


private theorem selectedExponent_root_ready_from_prefix_package
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀] [FiniteDimensional KB M₀]
    [IsGalois KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [Algebra B (integralClosure D M)]
    [IsScalarTower B D (integralClosure D M)]
    [IsScalarTower B (integralClosure D M) M]
    [Module.Finite B (integralClosure D M)]
    [IsFractionRing (integralClosure D M) M]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (p : Ideal (integralClosure D M))
    (hPrefixPackage : SelectedExponentPrefixPackage
      (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
      yB zB hregB hgenB N g p)
    (hfiniteFinal : Module.Finite D (integralClosure D M))
    (hEtaleFinal : Algebra.Etale D (integralClosure D M))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    SelectedExponentRootReadyPackage (B := B) (D := D) N := by
  classical
  let C₀ := integralClosure B M₀
  let E := integralClosure D M
  obtain ⟨hPrefixData⟩ := hPrefixPackage
  unfold SelectedExponentPrefixPackageBody at hPrefixData
  dsimp only at hPrefixData
  obtain
      ⟨Nfinal, hNfinalPrime, hNfinalOver,
        hNfinalLePfinal, hPfinalMax,
        qhatPrefix, hqhatPrefixPrime, hqhatPrefixOverBranch,
        hqhatPrefixData⟩ :=
    hPrefixData
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  have hgeometryHat :=
    maximalAdicCompletion_regularPair_geometry hregB hgenB
  let : IsDomain Bhat := hgeometryHat.1
  let : IsNoetherianRing Bhat :=
    maximalAdicCompletion_isNoetherianRing_of_regularPair hregB hgenB
  let zhat : Bhat := algebraMap B Bhat zB
  have hregHat : IsRegular Bhat [yhat, zhat] := by
    simpa only [Bhat, yhat, zhat] using hgeometryHat.2.1
  have hgenHat : Ideal.ofList [yhat, zhat] = maximalIdeal Bhat := by
    simpa only [Bhat, yhat, zhat] using hgeometryHat.2.2.1
  let : IsRegularLocalRing Bhat :=
    isRegularLocalRing_of_regularSystem [yhat, zhat] hregHat hgenHat
  have hyBMax : yB ∈ maximalIdeal B := by
    rw [← hgenB]
    exact Ideal.subset_span
      (show yB ∈ [yB, zB] from List.mem_cons_self)
  have hyHatMax : yhat ∈ maximalIdeal Bhat := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap B Bhat) hyBMax
  let qB := Ideal.span ({yB} : Set B)
  let : CharZero (B ⧸ qB) := by simpa only [qB] using hCharB
  have hCharHatMap :=
    charZero_quotient_mappedIdeal_maximalAdicCompletion qB
      (inferInstance : CharZero (B ⧸ qB))
  have hBranchMap :
      Ideal.map (algebraMap B Bhat) qB =
        Ideal.span ({yhat} : Set Bhat) := by
    calc
      Ideal.map (algebraMap B Bhat) qB =
          Ideal.span ((algebraMap B Bhat) '' ({yB} : Set B)) := by
        simp only [qB, Ideal.map_span]
      _ = Ideal.span ({yhat} : Set Bhat) := by
        simp only [Set.image_singleton, yhat]
  have hCharHat : CharZero
      (Bhat ⧸ Ideal.span ({yhat} : Set Bhat)) := by
    rw [← hBranchMap]
    exact hCharHatMap
  have eBaseRootHat :
      (Bhat ⊗[B] D) ≃ₐ[Bhat] AdjoinRoot (X ^ N - Polynomial.C yhat) := by
    simpa only [Bhat, yhat] using eBaseRoot
  let Tfinal := Bhat ⊗[B] E
  let : Algebra Bhat Tfinal := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Tfinal := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B Bhat Tfinal :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower B E Tfinal :=
    Algebra.TensorProduct.right_isScalarTower
  let Pfinal := p.map (algebraMap E Tfinal)
  let Tprefix := Bhat ⊗[B] C₀
  let : Algebra Bhat Tprefix := Algebra.TensorProduct.leftAlgebra
  let : Algebra C₀ Tprefix := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower B Bhat Tprefix :=
    TensorProduct.isScalarTower_left
  let : IsScalarTower B C₀ Tprefix :=
    Algebra.TensorProduct.right_isScalarTower
  let fT := completedFiniteModelTowerAlgHom
    (R := B) (R' := Bhat) (S₀ := C₀) (S₁ := E) g
  let Nprefix := Nfinal.comap fT.toRingHom
  let : Nprefix.IsPrime := hNfinalPrime.comap fT.toRingHom
  let : Nprefix.LiesOver (⊥ : Ideal Bhat) := by
    refine ⟨?_⟩
    ext x
    change x ∈ (⊥ : Ideal Bhat) ↔
      fT (algebraMap Bhat Tprefix x) ∈ Nfinal
    rw [fT.commutes x]
    exact Nfinal.mem_of_liesOver (⊥ : Ideal Bhat) x
  let Khat := FractionRing Bhat
  let : Module.FaithfullyFlat B Bhat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : FaithfulSMul B Khat := FaithfulSMul.trans B Bhat Khat
  let : Algebra KB Khat :=
    (IsFractionRing.lift
      (A := B) (K := KB) (L := Khat)
      (FaithfulSMul.algebraMap_injective B Khat)).toAlgebra
  let : IsScalarTower B KB Khat :=
    IsScalarTower.of_algebraMap_smul fun b x ↦ by
      rw [Algebra.smul_def, Algebra.smul_def]
      change
        (IsFractionRing.lift
          (A := B) (K := KB) (L := Khat)
          (FaithfulSMul.algebraMap_injective B Khat))
            (algebraMap B KB b) * x =
          algebraMap B Khat b * x
      rw [IsFractionRing.lift_algebraMap]
  let mPrefix := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
    (K' := Khat) Nprefix
  let : mPrefix.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := C₀) (K := KB) (L := M₀)
      (K' := Khat) Nprefix
  let OmegaPrefix := GenericTensorFieldComponent mPrefix
  let bHatOmegaPrefixAlgebra : Algebra Bhat OmegaPrefix :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mPrefix
  let : SMul Bhat OmegaPrefix := bHatOmegaPrefixAlgebra.toSMul
  let : IsScalarTower Bhat Khat OmegaPrefix :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ICprefixCore := selectedPrefixNormalizationRing
    (B := B) (KB := KB) (M₀ := M₀)
    yB zB hregB hgenB Nprefix
  let prefixCoreOwner := selectedPrefixNormalizationOwner
    (B := B) (KB := KB) (M₀ := M₀)
    yB zB hregB hgenB Nprefix
  let : CommRing ICprefixCore := prefixCoreOwner.commRingΩ
  let : Algebra Bhat ICprefixCore := prefixCoreOwner.algebra
  have hqhatPrefixExact : qhatPrefix.ramificationIdx Bhat = N :=
    hqhatPrefixData.1
  have hAwayPrefixHat :
      (Localization.awayMap
        (algebraMap Bhat (integralClosure Bhat OmegaPrefix)) yhat).Etale :=
    hqhatPrefixData.2
  obtain ⟨fComponentTower, -⟩ :=
    exists_retainedCompletedComponentTowerAlgHom
      (R := B) (R' := Bhat) (S₀ := C₀) (S₁ := E)
      (K := KB) (K' := Khat) (L₀ := M₀) (L₁ := M) g Nfinal
  let mFinal := retainedCompletedGenericTensorIdeal
    (R := B) (R' := Bhat) (S := E) (K := KB) (L := M)
    (K' := Khat) Nfinal
  let : mFinal.IsMaximal :=
    retainedCompletedGenericTensorIdeal_isMaximal
      (R := B) (R' := Bhat) (S := E) (K := KB) (L := M)
      (K' := Khat) Nfinal
  let OmegaFinal := GenericTensorFieldComponent mFinal
  let : Algebra Bhat OmegaFinal :=
    genericTensorFieldComponentLeftScalarAlgebra (R := Bhat) mFinal
  let : SMul Bhat OmegaFinal :=
    (genericTensorFieldComponentLeftScalarAlgebra
      (R := Bhat) mFinal).toSMul
  let : IsScalarTower Bhat Khat OmegaFinal :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨fFinal, -⟩ :=
    exists_retainedCompletedComponentToChosenLocalFractionAlgHom
      (R := B) (R' := Bhat) (S := E) (K := KB) (L := M)
      (K' := Khat) Nfinal Pfinal hNfinalLePfinal hPfinalMax
  exact SelectedExponentRootReadyPackage.mk
    (B := B) (D := D) (N := N)
    E Bhat OmegaPrefix OmegaFinal
    yhat zhat hregHat hgenHat hN hyHatMax hCharHat eBaseRootHat
    Pfinal hPfinalMax fFinal fComponentTower
    qhatPrefix hqhatPrefixPrime hqhatPrefixOverBranch
    hqhatPrefixExact hAwayPrefixHat
    (fun hUnitHat => by
      apply (isUnit_map_iff (algebraMap B Bhat) (N : B)).mp
      simpa using hUnitHat)

/-- Consume the typed terminal boundary in a fresh instance context. -/
private theorem selectedExponent_finish_root_ready_package
    {B D : Type u} [CommRing B] [CommRing D] [Algebra B D]
    {N : ℕ}
    (data : SelectedExponentRootReadyPackage (B := B) (D := D) N) :
    IsUnit (N : B) := by
  rcases data with
    ⟨E, A, Omega, OmegaFinal, y, z, hreg, hgen, hN, hyMax,
      hChar, eBaseRoot, Pfinal, hPfinalMax, fFinal, fTower,
      q, hqPrime, hqOver, hqExact, hAway, reflectUnit⟩
  apply reflectUnit
  exact selectedExponent_finish_completed_root_pushout
    (B := B) (D := D) (E := E) (A := A)
    (Omega := Omega) (OmegaFinal := OmegaFinal)
    y z hreg hgen N hN hyMax hChar eBaseRoot
    Pfinal hPfinalMax fFinal fTower
    q hqPrime hqOver hqExact hAway


/-- Unpack the prefix once, then cross the typed terminal boundary. -/
private theorem selectedExponent_completion_from_prefix_package
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀] [FiniteDimensional KB M₀]
    [IsGalois KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [IsScalarTower B (integralClosure B M₀) M₀]
    [Module.Finite B (integralClosure B M₀)]
    [IsFractionRing (integralClosure B M₀) M₀]
    [Algebra B (integralClosure D M)]
    [IsScalarTower B D (integralClosure D M)]
    [IsScalarTower B (integralClosure D M) M]
    [Module.Finite B (integralClosure D M)]
    [IsFractionRing (integralClosure D M) M]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (p : Ideal (integralClosure D M))
    (hPrefixPackage : SelectedExponentPrefixPackage
      (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
      yB zB hregB hgenB N g p)
    (hfiniteFinal : Module.Finite D (integralClosure D M))
    (hEtaleFinal : Algebra.Etale D (integralClosure D M))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    IsUnit (N : B) := by
  let data := selectedExponent_root_ready_from_prefix_package
    yB zB N hN hregB hgenB hCharB g p hPrefixPackage
    hfiniteFinal hEtaleFinal eBaseRoot
  exact selectedExponent_finish_root_ready_package data


/-- Assemble the prefix package separately so the long completed calculation
is checked in an independent declaration. -/
private theorem selectedExponent_completion_core
    {B D KB M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field M₀] [Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀] [FiniteDimensional KB M₀]
    [IsGalois KB M₀]
    [Field M] [Algebra D M] [Algebra B M] [IsScalarTower B D M]
    [Algebra KB M] [IsScalarTower B KB M]
    [Algebra B (integralClosure D M)]
    [IsScalarTower B D (integralClosure D M)]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (qGlobal p : Ideal (integralClosure D M))
    (hqGlobalPrime : qGlobal.IsPrime)
    (hqGlobalOverB : qGlobal.LiesOver (Ideal.span ({yB} : Set B)))
    (hqGlobalLe : qGlobal ≤ p)
    (hpMax : p.IsMaximal)
    (hpOverB : p.LiesOver (maximalIdeal B))
    (qPrefix : Ideal (integralClosure B M₀))
    [hqPrefixPrime : qPrefix.IsPrime]
    [hqPrefixOverB : qPrefix.LiesOver (Ideal.span ({yB} : Set B))]
    (hqGlobalComap : qGlobal.comap g.toRingHom = qPrefix)
    (hqPrefixExact : qPrefix.ramificationIdx B = N)
    (hAwayPrefix :
      (Localization.awayMap (algebraMap B (integralClosure B M₀)) yB).Etale)
    (hfiniteFinal : Module.Finite D (integralClosure D M))
    (hEtaleFinal : Algebra.Etale D (integralClosure D M))
    (hFractionFinal : IsFractionRing (integralClosure D M) M)
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    IsUnit (N : B) := by
  let E := integralClosure D M
  let C₀ := integralClosure B M₀
  let : IsScalarTower B C₀ M₀ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite B C₀ :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := KB) hdimB
  let : IsFractionRing C₀ M₀ :=
    IsIntegralClosure.isFractionRing_of_finite_extension B KB M₀ C₀
  let : IsScalarTower B E M := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap B M x = algebraMap D M (algebraMap B D x) :=
        IsScalarTower.algebraMap_apply B D M x
      _ = algebraMap E M (algebraMap D E (algebraMap B D x)) :=
        (IsScalarTower.algebraMap_apply D E M _).symm
      _ = algebraMap E M (algebraMap B E x) := by
        rw [IsScalarTower.algebraMap_apply B D E]
  let : Module.Finite B E := by
    exact Module.Finite.trans D E
  have hPrefixPackage := by
    letI : FaithfulSMul B C₀ :=
      integralClosure_faithfulSMul_of_fractionField
        (R := B) (K := KB) (L := M₀)
    letI : IsIntegrallyClosed C₀ :=
      integralClosure.isIntegrallyClosedOfFiniteExtension KB
    letI : Module.Flat B E := by
      exact Module.Flat.trans B D E
    exact selectedExponent_completion_prefix
      (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
      yB zB N hregB hgenB hdimB hyBPrime hCharB
      g qGlobal p hqGlobalPrime hqGlobalOverB hqGlobalLe hpMax hpOverB
      qPrefix hqGlobalComap hqPrefixExact hAwayPrefix
  exact selectedExponent_completion_from_prefix_package
    (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
    yB zB N hN hregB hgenB hCharB g p hPrefixPackage
    hfiniteFinal hEtaleFinal eBaseRoot

/-- The maximal ideal of a finite faithful extension of local rings lies
over the maximal ideal of the base. -/
private theorem maximalIdeal_liesOver_of_finite_local_extension
    {R S : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
    (hfinite : Module.Finite R S) :
    (maximalIdeal S).LiesOver (maximalIdeal R) := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let : IsLocalHom (algebraMap R S) :=
    Algebra.IsIntegral.isLocalHom R S
  apply (Ideal.liesOver_iff _ _).mpr
  exact (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm

/-- Contract a retained branch and its retained closed point through one
finite local intermediate ring. -/
private theorem retained_primes_lieOver_base_of_finite_local_extension
    {B D E : Type u}
    [CommRing B] [IsLocalRing B]
    [CommRing D] [IsLocalRing D] [Algebra B D] [FaithfulSMul B D]
    [CommRing E] [Algebra D E] [Algebra B E] [IsScalarTower B D E]
    (hfinite : Module.Finite B D)
    (qB : Ideal B) (qD : Ideal D)
    (qGlobal p : Ideal E)
    (hqDOverB : qD.LiesOver qB)
    (hqGlobalOverD : qGlobal.LiesOver qD)
    (hpOverD : p.LiesOver (maximalIdeal D)) :
    qGlobal.LiesOver qB ∧ p.LiesOver (maximalIdeal B) := by
  have hqGlobalOverB : qGlobal.LiesOver qB := by
    exact Ideal.LiesOver.trans qGlobal qD qB
  have hmaxDOverB : (maximalIdeal D).LiesOver (maximalIdeal B) :=
    maximalIdeal_liesOver_of_finite_local_extension
      (R := B) (S := D) hfinite
  have hpOverB : p.LiesOver (maximalIdeal B) := by
    exact Ideal.LiesOver.trans p (maximalIdeal D) (maximalIdeal B)
  exact ⟨hqGlobalOverB, hpOverB⟩

/-- Finish from fixed component fields after contracting the retained final
primes and identifying the final normalization's fraction field. -/
private theorem selectedExponent_completion_of_component_fields
    {B D KB KD M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [Field M₀] [bM₀Algebra : Algebra B M₀] [Algebra KB M₀]
    [IsScalarTower B KB M₀] [FiniteDimensional KB M₀]
    [IsGalois KB M₀]
    [Field M] [dMAlgebra : Algebra D M] [bMAlgebra : Algebra B M]
    [IsScalarTower B D M]
    [Algebra KD M] [IsScalarTower D KD M] [FiniteDimensional KD M]
    [kbMAlgebra : Algebra KB M] [IsScalarTower B KB M]
    [bEAlgebra : Algebra B (integralClosure D M)]
    [bDETower : IsScalarTower B D (integralClosure D M)]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (qD : Ideal D)
    (hqDOverB : qD.LiesOver (Ideal.span ({yB} : Set B)))
    (qGlobal p : Ideal (integralClosure D M))
    (hqGlobalPrime : qGlobal.IsPrime)
    (hqGlobalOverD : qGlobal.LiesOver qD)
    (hqGlobalLe : qGlobal ≤ p)
    (hpMax : p.IsMaximal)
    (hpOverD : p.LiesOver (maximalIdeal D))
    (qPrefix : Ideal (integralClosure B M₀))
    (hqGlobalComap : qGlobal.comap g.toRingHom = qPrefix)
    (hqPrefixPrime : qPrefix.IsPrime)
    (hqPrefixOverB : qPrefix.LiesOver (Ideal.span ({yB} : Set B)))
    (hqPrefixExact : qPrefix.ramificationIdx B = N)
    (hAwayPrefix :
      (Localization.awayMap
        (algebraMap B (integralClosure B M₀)) yB).Etale)
    (hfiniteFinal : Module.Finite D (integralClosure D M))
    (hEtaleFinal : Algebra.Etale D (integralClosure D M))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    IsUnit (N : B) := by
  obtain ⟨hqGlobalOverB, hpOverB⟩ :=
    retained_primes_lieOver_base_of_finite_local_extension
      (B := B) (D := D) (E := integralClosure D M)
      (inferInstance : Module.Finite B D)
      (Ideal.span ({yB} : Set B)) qD qGlobal p
      hqDOverB hqGlobalOverD hpOverD
  have hFractionFinal : IsFractionRing (integralClosure D M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      D KD M (integralClosure D M)
  exact selectedExponent_completion_core
    (B := B) (D := D) (KB := KB) (M₀ := M₀) (M := M)
    yB zB N hN hregB hgenB hdimB hyBPrime hCharB
    g qGlobal p hqGlobalPrime hqGlobalOverB hqGlobalLe hpMax hpOverB
    qPrefix (hqPrefixPrime := hqPrefixPrime)
    (hqPrefixOverB := hqPrefixOverB)
    hqGlobalComap hqPrefixExact hAwayPrefix hfiniteFinal hEtaleFinal
    hFractionFinal eBaseRoot

/-- The exact-prime goal after both component fields and their normalization
map have been fixed. -/
private def SelectedExponentComponentFieldsGoal
    {B D M₀ M : Type u}
    [CommRing B] [CommRing D] [IsLocalRing D] [Algebra B D]
    [Field M₀] [_bM₀Algebra : Algebra B M₀]
    [Field M] [_dMAlgebra : Algebra D M]
    [_bEAlgebra : Algebra B (integralClosure D M)]
    (yB : B) (N : ℕ) (qD : Ideal D) : Prop :=
  ∀ (g : integralClosure B M₀ →ₐ[B] integralClosure D M)
    (qGlobal p : Ideal (integralClosure D M)),
    qGlobal.IsPrime →
    qGlobal.LiesOver qD →
    qGlobal ≤ p →
    p.IsMaximal →
    p.LiesOver (maximalIdeal D) →
    let qPrefix := qGlobal.comap g.toRingHom
    qPrefix.IsPrime →
    qPrefix.LiesOver (Ideal.span ({yB} : Set B)) →
    qPrefix.ramificationIdx B = N →
    (Localization.awayMap
      (algebraMap B (integralClosure B M₀)) yB).Etale →
    Module.Finite D (integralClosure D M) →
    Algebra.Etale D (integralClosure D M) →
    IsUnit (N : B)

/-- Prove the exact-prime goal once both component fields are fixed. -/
private theorem selectedExponent_completion_of_component_fields_goal
    {B D KB KD M₀ M : Type u}
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [m₀Field : Field M₀] [bM₀Algebra : Algebra B M₀]
    [kbM₀Algebra : Algebra KB M₀]
    [bKBM₀Tower : IsScalarTower B KB M₀]
    [kbM₀Finite : FiniteDimensional KB M₀]
    [kbM₀Galois : IsGalois KB M₀]
    [Field M] [dMAlgebra : Algebra D M] [bMAlgebra : Algebra B M]
    [IsScalarTower B D M]
    [Algebra KD M] [IsScalarTower D KD M] [FiniteDimensional KD M]
    [kbMAlgebra : Algebra KB M] [IsScalarTower B KB M]
    [bEAlgebra : Algebra B (integralClosure D M)]
    [bDETower : IsScalarTower B D (integralClosure D M)]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (qD : Ideal D)
    (hqDOverB : qD.LiesOver (Ideal.span ({yB} : Set B)))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    SelectedExponentComponentFieldsGoal
      (B := B) (D := D) (M₀ := M₀) (M := M)
      (_bM₀Algebra := bM₀Algebra) (_dMAlgebra := dMAlgebra)
      (_bEAlgebra := bEAlgebra) yB N qD := by
  unfold SelectedExponentComponentFieldsGoal
  intro g qGlobal p hqGlobalPrime hqGlobalOverD hqGlobalLe hpMax hpOverD
    qPrefix hqPrefixPrime hqPrefixOverB hqPrefixExact
    hAwayPrefix hfiniteFinal hEtaleFinal
  exact selectedExponent_completion_of_component_fields
    (B := B) (D := D) (KB := KB) (KD := KD) (M₀ := M₀) (M := M)
    (bM₀Algebra := bM₀Algebra) (dMAlgebra := dMAlgebra)
    (bMAlgebra := bMAlgebra) (kbMAlgebra := kbMAlgebra)
    (bEAlgebra := bEAlgebra) (bDETower := bDETower)
    yB zB N hN hregB hgenB hdimB hyBPrime hCharB
    g qD hqDOverB qGlobal p
    hqGlobalPrime hqGlobalOverD hqGlobalLe hpMax hpOverD
    qPrefix rfl hqPrefixPrime hqPrefixOverB hqPrefixExact
    hAwayPrefix hfiniteFinal hEtaleFinal eBaseRoot

/-- The remaining selected-exponent goal after fixing the final generic
tensor component, expressed through its actual intermediate contraction. -/
private def SelectedExponentFixedFinalGoal
    {K L B D KB KD M : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [Algebra K KB] [Algebra K KD]
    [Algebra B KD] [IsScalarTower B D KD]
    [Algebra KB KD] [IsScalarTower B KB KD]
    [IsScalarTower K KB KD] [FiniteDimensional KB KD]
    (m : Ideal (KD ⊗[K] L)) [m.IsMaximal]
    [Field M]
    [dMAlgebra : Algebra D M] [_bMAlgebra : Algebra B M]
    [_bDMTower : IsScalarTower B D M]
    [_kdMAlgebra : Algebra KD M] [_dKDMTower : IsScalarTower D KD M]
    [FiniteDimensional KD M]
    [_kbMAlgebra : Algebra KB M] [_bKBMTower : IsScalarTower B KB M]
    [bEAlgebra : Algebra B (integralClosure D M)]
    [_bDETower : IsScalarTower B D (integralClosure D M)]
    (yB : B) (N : ℕ) (qD : Ideal D) : Prop :=
    let n₀ := genericTensorTowerIntermediateIdeal
      (K := K) (F := KB) (F' := KD) (L := L) m
    letI : n₀.IsMaximal :=
      genericTensorTowerIntermediateIdeal_isMaximal
        (K := K) (F := KB) (F' := KD) (L := L) m
    let M₀ := GenericTensorFieldComponent n₀
    let m₀Field : Field M₀ := inferInstance
    letI : Field M₀ := m₀Field
    let kbM₀Algebra : Algebra KB M₀ := inferInstance
    letI : Algebra KB M₀ := kbM₀Algebra
    let bM₀Algebra : Algebra B M₀ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) n₀
    letI : Algebra B M₀ := bM₀Algebra
    letI : SMul B M₀ := bM₀Algebra.toSMul
    let bKBM₀Tower : IsScalarTower B KB M₀ :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : IsScalarTower B KB M₀ := bKBM₀Tower
    let kbM₀Finite : FiniteDimensional KB M₀ := inferInstance
    letI : FiniteDimensional KB M₀ := kbM₀Finite
    let kbM₀Galois : IsGalois KB M₀ := inferInstance
    letI : IsGalois KB M₀ := kbM₀Galois
    SelectedExponentComponentFieldsGoal
      (B := B) (D := D) (M₀ := M₀) (M := M)
      (_bM₀Algebra := bM₀Algebra) (_dMAlgebra := dMAlgebra)
      (_bEAlgebra := bEAlgebra) yB N qD

/-- Prove the intermediate-contraction goal for a fixed final component. -/
private theorem selectedExponent_completion_of_fixed_final_component
    {K L B D KB KD M : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [Algebra K KB] [Algebra K KD]
    [Algebra B KD] [IsScalarTower B D KD]
    [Algebra KB KD] [IsScalarTower B KB KD]
    [IsScalarTower K KB KD] [FiniteDimensional KB KD]
    (m : Ideal (KD ⊗[K] L)) [m.IsMaximal]
    [Field M]
    [dMAlgebra : Algebra D M] [bMAlgebra : Algebra B M]
    [bDMTower : IsScalarTower B D M]
    [kdMAlgebra : Algebra KD M] [dKDMTower : IsScalarTower D KD M]
    [FiniteDimensional KD M]
    [kbMAlgebra : Algebra KB M] [bKBMTower : IsScalarTower B KB M]
    [bEAlgebra : Algebra B (integralClosure D M)]
    [bDETower : IsScalarTower B D (integralClosure D M)]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (qD : Ideal D)
    (hqDOverB : qD.LiesOver (Ideal.span ({yB} : Set B)))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    SelectedExponentFixedFinalGoal
      (K := K) (L := L) (B := B) (D := D) (KB := KB) (KD := KD)
      (m := m) (M := M) (dMAlgebra := dMAlgebra)
      (_bMAlgebra := bMAlgebra) (_bDMTower := bDMTower)
      (_dKDMTower := dKDMTower) (_kbMAlgebra := kbMAlgebra)
      (_bKBMTower := bKBMTower) (bEAlgebra := bEAlgebra)
      (_bDETower := bDETower)
      yB N qD := by
  classical
  unfold SelectedExponentFixedFinalGoal
  intro n₀ M₀ m₀Field kbM₀Algebra bM₀Algebra bKBM₀Tower
    kbM₀Finite kbM₀Galois
  exact selectedExponent_completion_of_component_fields_goal
    (B := B) (D := D) (KB := KB) (KD := KD) (M₀ := M₀) (M := M)
    (m₀Field := m₀Field) (bM₀Algebra := bM₀Algebra)
    (kbM₀Algebra := kbM₀Algebra) (bKBM₀Tower := bKBM₀Tower)
    (kbM₀Finite := kbM₀Finite) (kbM₀Galois := kbM₀Galois)
    (dMAlgebra := dMAlgebra)
    (bMAlgebra := bMAlgebra) (kbMAlgebra := kbMAlgebra)
    (bEAlgebra := bEAlgebra) (bDETower := bDETower)
    yB zB N hN hregB hgenB hdimB hyBPrime hCharB
    qD hqDOverB eBaseRoot

/-- The selected-exponent goal after fixing the two fraction fields. -/
private def SelectedExponentFixedFractionFieldsGoal
    {K L B D KB KD : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [Algebra K KB] [Algebra K KD]
    [Algebra B KD] [IsScalarTower B D KD]
    [Algebra KB KD] [IsScalarTower B KB KD]
    [IsScalarTower K KB KD] [FiniteDimensional KB KD]
    (yB : B) (N : ℕ) (qD : Ideal D) : Prop :=
    let m := genericTensorMaximalIdeal (K := K) (K' := KD) (L := L)
    letI : m.IsMaximal := genericTensorMaximalIdeal_isMaximal
    let M := GenericTensorFieldComponent m
    let dMAlgebra : Algebra D M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := D) m
    letI : Algebra D M := dMAlgebra
    let bMAlgebra : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI : Algebra B M := bMAlgebra
    letI : SMul D M := dMAlgebra.toSMul
    letI : SMul B M := bMAlgebra.toSMul
    let bDMTower : IsScalarTower B D M := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change algebraMap KD M (algebraMap B KD x) =
        algebraMap KD M (algebraMap D KD (algebraMap B D x))
      rw [IsScalarTower.algebraMap_apply B D KD]
    letI : IsScalarTower B D M := bDMTower
    let dKDMTower : IsScalarTower D KD M :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    letI : IsScalarTower D KD M := dKDMTower
    let kbMAlgebra : Algebra KB M :=
      ((algebraMap KD M).comp (algebraMap KB KD)).toAlgebra
    letI : Algebra KB M := kbMAlgebra
    letI : SMul KB M := kbMAlgebra.toSMul
    let bKBMTower : IsScalarTower B KB M := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change algebraMap KD M (algebraMap B KD x) =
        algebraMap KD M (algebraMap KB KD (algebraMap B KB x))
      rw [← IsScalarTower.algebraMap_apply B KB KD]
    letI : IsScalarTower B KB M := bKBMTower
    let bEAlgebra : Algebra B (integralClosure D M) :=
      ((algebraMap D (integralClosure D M)).comp (algebraMap B D)).toAlgebra
    letI : Algebra B (integralClosure D M) := bEAlgebra
    let bDETower : IsScalarTower B D (integralClosure D M) :=
      IsScalarTower.of_algebraMap_eq' rfl
    SelectedExponentFixedFinalGoal
      (K := K) (L := L) (B := B) (D := D) (KB := KB) (KD := KD)
      (m := m) (M := M) (dMAlgebra := dMAlgebra)
      (_bMAlgebra := bMAlgebra) (_bDMTower := bDMTower)
      (_dKDMTower := dKDMTower) (_kbMAlgebra := kbMAlgebra)
      (_bKBMTower := bKBMTower)
      (bEAlgebra := bEAlgebra)
      (_bDETower := bDETower)
      yB N qD

/-- Select the final component and its intermediate contraction over the two
fixed fraction fields. -/
private theorem selectedExponent_completion_of_fixed_fraction_fields
    {K L B D KB KD : Type u}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing B] [IsDomain B] [IsRegularLocalRing B]
    [CommRing D] [IsDomain D] [IsRegularLocalRing D] [Algebra B D]
    [Module.Finite B D] [Module.Flat B D] [FaithfulSMul B D]
    [Field KB] [Algebra B KB] [IsFractionRing B KB]
    [Field KD] [Algebra D KD] [IsFractionRing D KD]
    [Algebra K KB] [Algebra K KD]
    [Algebra B KD] [IsScalarTower B D KD]
    [Algebra KB KD] [IsScalarTower B KB KD]
    [IsScalarTower K KB KD] [FiniteDimensional KB KD]
    (yB zB : B) (N : ℕ) (hN : 0 < N)
    (hregB : IsRegular B [yB, zB])
    (hgenB : Ideal.ofList [yB, zB] = maximalIdeal B)
    (hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞))
    (hyBPrime : Prime yB)
    (hCharB : CharZero (B ⧸ Ideal.span ({yB} : Set B)))
    (qD : Ideal D)
    (hqDOverB : qD.LiesOver (Ideal.span ({yB} : Set B)))
    (eBaseRoot :
      (AdicCompletion (maximalIdeal B) B ⊗[B] D) ≃ₐ[AdicCompletion (maximalIdeal B) B]
        AdjoinRoot
          (X ^ N - C (algebraMap B (AdicCompletion (maximalIdeal B) B) yB))) :
    SelectedExponentFixedFractionFieldsGoal
      (K := K) (L := L) (B := B) (D := D) (KB := KB) (KD := KD)
      yB N qD := by
  classical
  unfold SelectedExponentFixedFractionFieldsGoal
  intro m M dMAlgebra bMAlgebra bDMTower dKDMTower
    kbMAlgebra bKBMTower bEAlgebra bDETower
  exact selectedExponent_completion_of_fixed_final_component
    (K := K) (L := L) (B := B) (D := D) (KB := KB) (KD := KD)
    (m := m) (M := M) (dMAlgebra := dMAlgebra)
    (bMAlgebra := bMAlgebra) (bDMTower := bDMTower)
    (dKDMTower := dKDMTower) (kbMAlgebra := kbMAlgebra)
    (bKBMTower := bKBMTower)
    (bEAlgebra := bEAlgebra) (bDETower := bDETower)
    yB zB N hN hregB hgenB hdimB hyBPrime hCharB
    qD hqDOverB eBaseRoot

/-- A natural-number unit descends along a finite map of local rings. -/
private theorem isUnit_natCast_of_finite_local_extension
    {R S : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [FaithfulSMul R S]
    (hfinite : Module.Finite R S) (N : ℕ)
    (hUnit : IsUnit (N : S)) :
    IsUnit (N : R) := by
  let : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let : IsLocalHom (algebraMap R S) :=
    Algebra.IsIntegral.isLocalHom R S
  apply (isUnit_map_iff (algebraMap R S) (N : R)).mp
  simpa only [map_natCast] using hUnit

/-- The exponent of the selected branch is a unit at every height-two point.

The proof uses the same retained completion prime for the final finite-etale
normalization and for its canonical prefix normalization. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_selectedExponent_isUnit
    {A K L : Type u}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAwayBase : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale) :
    IsUnit
      ((heightTwoSelectedBranchGaloisRamificationIndex
          (K := K) (L := L) t hNC i : ℕ) :
        Localization.AtPrime P) := by
  classical
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let N := heightTwoSelectedBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  have hN : 0 < N :=
    heightTwoSelectedBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have he : ∀ k, 0 < e k :=
    heightTwoOtherBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  obtain
      ⟨σ, hgeometryB, hgeometryD, hTower, hFin,
        -, qGlobal, p,
        hqGlobalPrime, hqGlobalOverD, -,
        -, -, hqGlobalLe,
        hpMax, hpOverD,
        hqGlobalComap, hqPrefixPrime, hqPrefixOverB, hqPrefixExact,
        -, -, -,
        -, -, -, -,
        -, hAwayPrefix, hfiniteFinal,
        hEtaleFinal⟩ :=
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_selectedComponent_exactPrimeSource
      (K := K) (L := L) hNC i hi P hP htiP hCharZero hAwayBase
  let R := Localization.AtPrime P
  let n := heightTwoConditionalOtherExponent t i r P e σ
  let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
  let y : R := algebraMap A R (t i)
  let hn : ∀ k, 0 < n k :=
    heightTwoConditionalOtherExponent_pos_of_pos t i r P e he σ
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  have hCharR :
      CharZero (R ⧸ Ideal.span ({y} : Set R)) := by
    change CharZero
      (Localization.AtPrime P ⧸
        Ideal.span
          ({algebraMap A (Localization.AtPrime P) (t i)} :
            Set (Localization.AtPrime P)))
    exact charZero_quotient_algebraMap_localizationAtPrime P
      (hNC.2.2.2.1 i hi) htiP (hCharZero i hi)
  let B := iteratedRadical R d n a
  let yB : B := algebraMap R B y
  let Froot : B[X] := X ^ N - C yB
  let D := AdjoinRoot Froot
  let : IsRegularLocalRing B := hgeometryB.1
  let : IsDomain B := hgeometryB.2.1
  let : IsRegularLocalRing D := hgeometryD.1
  let : IsDomain D := hgeometryD.2.1
  let : Module.Finite B D := by
    simpa only [D, Froot] using
      (monic_X_pow_sub_C yB hN.ne').finite_adjoinRoot
  let : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN yB
  let KB := FractionRing B
  let KD := FractionRing D
  let : FaithfulSMul R KB := FaithfulSMul.trans R B KB
  let : FaithfulSMul B KD := FaithfulSMul.trans B D KD
  let : Algebra K KB :=
    chosenFractionFieldToFaithfulFieldAlgebra
      (R := R) (K := K) (F := KB)
  let : Algebra K KD :=
    galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
  let : IsScalarTower B D KD := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra KB KD := FractionRing.liftAlgebra B KD
  let : IsScalarTower B KB KD :=
    FractionRing.isScalarTower_liftAlgebra B KD
  let qB := Ideal.span ({yB} : Set B)
  let qD := Ideal.span ({AdjoinRoot.root Froot} : Set D)
  let hqDOverB : qD.LiesOver qB :=
    span_root_liesOver_span_radicand hN hgeometryB.2.2.2.1
  have hCharB : CharZero (B ⧸ qB) := by
    have hmap := charZero_quotient_map_of_faithfullyFlat
      (S := B) (Ideal.span ({y} : Set R)) hCharR
    have hmapIdeal :
        (Ideal.span ({y} : Set R)).map (algebraMap R B) = qB := by
      simp [qB, yB, Ideal.map_span]
    rw [← hmapIdeal]
    exact hmap
  obtain ⟨zB, hregB, hgenB⟩ :=
    exists_regular_pair_of_prime_regular_quotient_dimension_two
      hgeometryB.2.2.2.1 hgeometryB.2.2.2.2.2 hgeometryB.2.2.1
  let Bhat := AdicCompletion (maximalIdeal B) B
  let yhat : Bhat := algebraMap B Bhat yB
  let eBaseRoot :
      (Bhat ⊗[B] D) ≃ₐ[Bhat] AdjoinRoot (X ^ N - C yhat) := by
    simpa only [Bhat, D, Froot, yhat] using
      (oneRootBaseChangeAlgEquiv (A := B) (S := Bhat) N yB)
  have hUnitB : IsUnit (N : B) :=
    selectedExponent_completion_of_fixed_fraction_fields
      (K := K) (L := L) (B := B) (D := D) (KB := KB) (KD := KD)
      yB zB N hN hregB hgenB hgeometryB.2.2.1
      hgeometryB.2.2.2.1 hCharB qD hqDOverB eBaseRoot
      (genericTensorTowerIntermediateNormalizationAlgHom
        (A := B) (B := D) (K := K) (F := KB) (F' := KD) (L := L)
        (genericTensorMaximalIdeal (K := K) (K' := KD) (L := L)))
      qGlobal p hqGlobalPrime hqGlobalOverD hqGlobalLe hpMax hpOverD
      (by rw [hqGlobalComap]; exact hqPrefixPrime)
      (by rw [hqGlobalComap]; exact hqPrefixOverB)
      (by rw [hqGlobalComap]; exact hqPrefixExact)
      hAwayPrefix hfiniteFinal hEtaleFinal
  have hUnitR : IsUnit (N : R) :=
    isUnit_natCast_of_finite_local_extension
      (R := R) (S := B) (finite_iteratedRadical n a hn) N hUnitB
  simpa only [N, R] using hUnitR

end EtaleFundamentalGroups.Kummer

end
