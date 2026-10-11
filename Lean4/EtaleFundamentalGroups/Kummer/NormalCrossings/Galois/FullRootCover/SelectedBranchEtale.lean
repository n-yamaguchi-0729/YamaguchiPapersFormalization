/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.RootCovers.Full.SelectedRootBaseChange
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRoot.LocalizationEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCover

/-!
# Selected height-one branch of the exact Galois full cover

This module supplies the finite faithful map from the selected simple root
cover to the full cover and applies the active-root localized-normalization
theorem for one fixed generic tensor component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- The chosen fraction field of the height-two base acts canonically on the
literal fraction ring of a full radical cover. -/
@[reducible]
noncomputable def galoisFullRootCoverFractionFieldAlgebra
    {R : Type uA} {K : Type uK}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (hn : ∀ k, 0 < n k) (N : ℕ) (hN : 0 < N) (y : R) :
    let B := iteratedRadical R d n a
    let D := AdjoinRoot (X ^ N - C (algebraMap R B y))
    ∀ [IsDomain D], Algebra K (FractionRing D) := by
  dsimp only
  intro _
  let B := iteratedRadical R d n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  letI : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n a hn
  letI : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
  letI : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective R B).nontrivial
  letI : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y)
  letI : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
  letI : FaithfulSMul R D := FaithfulSMul.trans R B D
  letI : FaithfulSMul R (FractionRing D) :=
    FaithfulSMul.trans R D (FractionRing D)
  exact chosenFractionFieldToFaithfulFieldAlgebra
    (R := R) (K := K) (F := FractionRing D)

/-- The preceding chosen action is compatible with the map from the
height-two local base. -/
theorem galoisFullRootCoverFractionField_isScalarTower
    {R : Type uA} {K : Type uK}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {d : ℕ} (n : Fin d → ℕ) (a : Fin d → R)
    (hn : ∀ k, 0 < n k) (N : ℕ) (hN : 0 < N) (y : R) :
    let B := iteratedRadical R d n a
    let D := AdjoinRoot (X ^ N - C (algebraMap R B y))
    ∀ [IsDomain D],
      letI : Algebra K (FractionRing D) :=
        galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
      IsScalarTower R K (FractionRing D) := by
  dsimp only
  intro _
  let B := iteratedRadical R d n a
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n a hn
  let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
  let : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective R B).nontrivial
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y)
  let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
  let : FaithfulSMul R D := FaithfulSMul.trans R B D
  let : FaithfulSMul R (FractionRing D) :=
    FaithfulSMul.trans R D (FractionRing D)
  let : Algebra K (FractionRing D) :=
    galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
  exact chosenFractionFieldToFaithfulField_isScalarTower
    (R := R) (K := K) (F := FractionRing D)

/-- Conditional full-cover exponents are positive whenever the prescribed
active exponents are positive. -/
theorem heightTwoConditionalOtherExponent_pos_of_pos
    {A : Type uA} [CommRing A] {d : ℕ}
    (t : Fin (d + 1) → A) (i : Fin (d + 1)) (r : ℕ)
    (P : Ideal A) (e : Fin d → ℕ) (he : ∀ k, 0 < e k)
    (σ : Equiv.Perm (Fin d)) :
    ∀ k, 0 < heightTwoConditionalOtherExponent t i r P e σ k := by
  intro k
  by_cases hk : (i.succAbove (σ k)).1 < r ∧
      t (i.succAbove (σ k)) ∈ P
  · simpa [heightTwoConditionalOtherExponent, hk] using he (σ k)
  · simp [heightTwoConditionalOtherExponent, hk]

/-- At the selected root prime of the exact Galois full cover, the literal
localized normalization in a fixed generic tensor component is etale. -/
theorem
    localization_integralClosure_galoisFullRootCover_selectedBranch_fixedComponent_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (hCharZero : CharZero (A ⧸ Ideal.span ({t i} : Set A)))
    (σ : Equiv.Perm (Fin d)) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e σ
    let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
    let B := iteratedRadical R d n a
    let y : R := algebraMap A R (t i)
    let F : B[X] := X ^ N - C (algebraMap R B y)
    let D := AdjoinRoot F
    ∀ (hn : ∀ k, 0 < n k)
      (hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞)),
      letI : IsRegularLocalRing D := hgeometryD.1
      letI : IsDomain D := hgeometryD.2.1
      letI : IsIntegrallyClosed D :=
        SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
          hgeometryD.2.2
      letI : Algebra R K :=
        localizationAtPrimeToFractionFieldAlgebra (K := K) P
      letI : IsFractionRing R K :=
        localizationAtPrimeToFractionField_isFractionRing (K := K) P
      let K' := FractionRing D
      letI : Algebra K K' :=
        galoisFullRootCoverFractionFieldAlgebra n a hn N
          (heightTwoSelectedBranchGaloisRamificationIndex_pos
            (K := K) (L := L) t hNC i) y
      ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
        letI : m.IsMaximal := hm
        let M := GenericTensorFieldComponent m
        letI : Algebra D M :=
          genericTensorFieldComponentLeftScalarAlgebra (R := D) m
        letI : SMul D M :=
          (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
        letI : IsScalarTower D K' M :=
          IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        ∀ (q : Ideal D) [q.IsPrime], q.height = 1 →
          q = Ideal.span ({AdjoinRoot.root F} : Set D) →
          let Q := Localization.AtPrime q
          letI : Algebra Q K' :=
            localizationAtPrimeToFractionFieldAlgebra (K := K') q
          letI : IsFractionRing Q K' :=
            localizationAtPrimeToFractionField_isFractionRing (K := K') q
          letI : Algebra Q M :=
            localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
          letI : SMul Q M :=
            (localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q).toSMul
          letI : IsScalarTower Q K' M :=
            localizationAtPrimeToFractionFieldToExtension_isScalarTower
              (K := K') (L := M) q
          letI : IsScalarTower D Q M :=
            localizationAtPrimeToExtension_isScalarTower
              (K := K') (L := M) q
          letI := integralClosureLocalizationAlgebra (L := M) q
          Algebra.Etale Q
            (Localization (Algebra.algebraMapSubmonoid
              (integralClosure D M) q.primeCompl)) := by
  dsimp only
  unfold heightTwoSelectedBranchGaloisRamificationIndex
  intro hn hgeometryD
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let N := splitStrictNormalCrossingsGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  have hN : 0 < N :=
    splitStrictNormalCrossingsGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  let R := Localization.AtPrime P
  let n := heightTwoConditionalOtherExponent t i r P e σ
  let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
  let B := iteratedRadical R d n a
  let y : R := algebraMap A R (t i)
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let : IsRegularLocalRing D := hgeometryD.1
  let : IsDomain D := hgeometryD.2.1
  let : IsIntegrallyClosed D :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryD.2.2
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : Module.FaithfullyFlat R B := faithfullyFlat_iteratedRadical n a hn
  let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
  let : Nontrivial B :=
    (FaithfulSMul.algebraMap_injective R B).nontrivial
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y)
  let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
  let : FaithfulSMul R D := FaithfulSMul.trans R B D
  let K' := FractionRing D
  let : FaithfulSMul R K' := FaithfulSMul.trans R D K'
  let : Algebra K K' :=
    galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
  let : IsScalarTower R K K' :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  intro m hm
  let : m.IsMaximal := hm
  let M := GenericTensorFieldComponent m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro q _ hqHeight hselected
  let Q := Localization.AtPrime q
  let : Algebra Q K' :=
    localizationAtPrimeToFractionFieldAlgebra (K := K') q
  let : IsFractionRing Q K' :=
    localizationAtPrimeToFractionField_isFractionRing (K := K') q
  let : Algebra Q M :=
    localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
  let : SMul Q M :=
    (localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q).toSMul
  let : IsScalarTower Q K' M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K') (L := M) q
  let : IsScalarTower D Q M :=
    localizationAtPrimeToExtension_isScalarTower (K := K') (L := M) q
  let : Algebra (integralClosure D M) (integralClosure Q M) :=
    integralClosureLocalizationAlgebra (L := M) q
  let g : R[X] := X ^ N - C y
  let S := AdjoinRoot g
  let qS := Ideal.span ({AdjoinRoot.root g} : Set S)
  have hgeometryS :=
    splitStrictNormalCrossings_heightTwo_galoisSingleRootCover_geometry
      (K := K) (L := L) hNC i hi P hP htiP
  let : IsRegularLocalRing S := hgeometryS.1
  let : IsDomain S := hgeometryS.2.1
  let : IsIntegrallyClosed S :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryS.2.2.1
  let : qS.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime hgeometryS.2.2.2.1
  let : Algebra S D := fullRootCoverSelectedRootAlgebra n a N y
  let : Module.Finite S D :=
    fullRootCoverSelectedRoot_moduleFinite n a hn N y
  let : Module.FaithfullyFlat S D :=
    fullRootCoverSelectedRoot_faithfullyFlat n a hn N y
  let : FaithfulSMul S D := Module.FaithfullyFlat.faithfulSMul
  have hg : g.map (algebraMap R B) = F := by
    simp [g, F]
  let eBase : (B ⊗[R] S) ≃ₐ[B] D :=
    (adjoinRootBaseChangeAlgEquiv g).trans
      (AdjoinRoot.algEquivOfEq B _ _ hg)
  let : IsScalarTower R S D := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R D x =
      eBase ((1 : B) ⊗ₜ[R] algebraMap R S x)
    rw [← Algebra.TensorProduct.algebraMap_apply']
    rw [IsScalarTower.algebraMap_apply R B (B ⊗[R] S)]
    rw [eBase.commutes]
    exact IsScalarTower.algebraMap_apply R B D x
  have hunder : q.under S = qS :=
    fullRootCoverSelectedRoot_under_eq_span_root n a hn N y
      hgeometryS.2.2.2.1 q hqHeight hselected
  let : q.LiesOver qS := ⟨hunder.symm⟩
  exact
    localization_integralClosure_strictNormalCrossingsGaloisActiveRoot_fixedComponent_etale
      (K := K) (L := L) hNC i hi P hP htiP hCharZero
        (D := D) q m hm

end EtaleFundamentalGroups.Kummer

end
