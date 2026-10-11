/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.HeightOneBaseChange
import SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv
import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightOne.PrimeOverRootCover
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.OtherBranchEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.SelectedBranchEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCoverActualRoot

/-!
# Height-one etaleness for a fixed component of the exact Galois full cover

At a height-two strict-normal-crossings point, use the exact common Galois
ramification index on every active branch.  For one fixed generic tensor
component, selected and actual-root height-one primes are handled by the
active-root descent theorem, while primes away from the boundary are handled
by the original finite-etale normalization.  The output is the literal
localized normalization required by special local purity.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

theorem
    localization_integralClosure_genericTensorFieldComponent_etale_of_awayMap
    {A : Type uA} {C : Type uL} {D : Type uA}
    {F : Type uK} {E : Type uL} {K : Type uA}
    [CommRing A] [IsDomain A]
    [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    [Module.Finite A C]
    (f : A) (hf : f ≠ 0)
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra C E] [IsFractionRing C E]
    [Algebra A E] [IsScalarTower A C E]
    [Algebra F E] [IsScalarTower A F E]
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [Algebra A D]
    [Field K] [Algebra D K] [IsFractionRing D K]
    [Algebra A K] [IsScalarTower A D K]
    [Algebra F K] [IsScalarTower A F K]
    (hAway : (Localization.awayMap (algebraMap A C) f).Etale)
    (q : Ideal D) [q.IsPrime]
    (hdisj : Disjoint
      ((Submonoid.powers (algebraMap A D f) : Submonoid D) : Set D)
      (q : Set D))
    (m : Ideal (K ⊗[F] E)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    letI : Algebra D M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := D) m
    letI : SMul D M :=
      (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
    letI : IsScalarTower D K M :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let Q := Localization.AtPrime q
    letI : Algebra Q K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) q
    letI : IsFractionRing Q K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) q
    letI : Algebra Q M :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := M) q
    letI : SMul Q M :=
      (localizationAtPrimeToExtensionAlgebra (K := K) (L := M) q).toSMul
    letI : IsScalarTower Q K M :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := M) q
    letI : IsScalarTower D Q M :=
      localizationAtPrimeToExtension_isScalarTower (K := K) (L := M) q
    letI := integralClosureLocalizationAlgebra (L := M) q
    Algebra.Etale Q
      (Localization (Algebra.algebraMapSubmonoid
        (integralClosure D M) q.primeCompl)) := by
  let S := Localization.Away f
  let fC : C := algebraMap A C f
  let T := Localization.Away fC
  have hfC : fC ≠ 0 := by
    simpa [fC] using (FaithfulSMul.algebraMap_injective A C).ne hf
  let mapST : S →+* T := Localization.awayMap (algebraMap A C) f
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A C T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A T x = mapST (algebraMap A S x)
    rw [IsScalarTower.algebraMap_apply A C T]
    simp [mapST, S, T, fC, IsLocalization.Away.map]
  let : Module.Finite S T :=
    Module.Finite.of_isLocalization A C (Submonoid.powers f)
  let : Algebra.Etale S T := hAway.toAlgebra
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsDomain T := IsLocalization.Away.isDomain T hfC
  let : Algebra S F :=
    localizationAwayToExtensionAlgebra
      (A := A) (K := F) (L := F) f hf
  let : IsScalarTower A S F :=
    localizationAwayToExtension_isScalarTower
      (A := A) (K := F) (L := F) f hf
  let : IsFractionRing S F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers f) S F
  let : Algebra T E :=
    localizationAwayToExtensionAlgebra
      (A := C) (K := E) (L := E) fC hfC
  let : IsScalarTower C T E :=
    localizationAwayToExtension_isScalarTower
      (A := C) (K := E) (L := E) fC hfC
  let : IsFractionRing T E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers fC) T E
  let : Algebra S E :=
    ((algebraMap T E).comp (algebraMap S T)).toAlgebra
  let : IsScalarTower S T E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower S F E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    have hmaps :
        (algebraMap F E).comp (algebraMap S F) = algebraMap S E := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f)
      ext a
      change algebraMap F E (algebraMap S F (algebraMap A S a)) =
        algebraMap T E (mapST (algebraMap A S a))
      calc
        algebraMap F E (algebraMap S F (algebraMap A S a)) =
            algebraMap F E (algebraMap A F a) := by
          rw [← IsScalarTower.algebraMap_apply A S F]
        _ = algebraMap A E a :=
          (IsScalarTower.algebraMap_apply A F E a).symm
        _ = algebraMap C E (algebraMap A C a) :=
          IsScalarTower.algebraMap_apply A C E a
        _ = algebraMap T E (algebraMap C T (algebraMap A C a)) :=
          IsScalarTower.algebraMap_apply C T E (algebraMap A C a)
        _ = algebraMap T E (mapST (algebraMap A S a)) := by
          congr 1
          calc
            algebraMap C T (algebraMap A C a) = algebraMap A T a :=
              (IsScalarTower.algebraMap_apply A C T a).symm
            _ = algebraMap S T (algebraMap A S a) :=
              IsScalarTower.algebraMap_apply A S T a
            _ = mapST (algebraMap A S a) := rfl
    exact (DFunLike.congr_fun hmaps x).symm
  exact
    localization_integralClosure_genericTensorFieldComponent_etale_of_base_away
      (A := A) (C := C) (D := D) (F := F) (E := E) (K := K)
      f q hdisj m

/-- For the exact Galois full root cover, every height-one localization of
the normalization in a fixed generic tensor component is etale.  The
permutation, full-cover geometry, ramification divisibilities, residue
characteristic, and all contraction equalities are produced internally. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_fixedComponent_heightOne_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
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
    (hAway : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let F : B[X] := X ^ N - C (algebraMap R B y)
      let D := AdjoinRoot F
      ∃ hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
          ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞),
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
          galoisFullRootCoverFractionFieldAlgebra n a
            (heightTwoConditionalOtherExponent_pos_of_pos t i r P e
              (heightTwoOtherBranchGaloisRamificationIndex_pos
                (K := K) (L := L) t hNC i) σ)
            N
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
            let Q := Localization.AtPrime q
            letI : Algebra Q K' :=
              localizationAtPrimeToFractionFieldAlgebra (K := K') q
            letI : IsFractionRing Q K' :=
              localizationAtPrimeToFractionField_isFractionRing (K := K') q
            letI : Algebra Q M :=
              localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
            letI : SMul Q M :=
              (localizationAtPrimeToExtensionAlgebra
                (K := K') (L := M) q).toSMul
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
  classical
  let e := heightTwoOtherBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  let N := heightTwoSelectedBranchGaloisRamificationIndex
    (K := K) (L := L) t hNC i
  have he : ∀ k, 0 < e k :=
    heightTwoOtherBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  have hN : 0 < N :=
    heightTwoSelectedBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  rcases
      splitStrictNormalCrossings_heightTwo_fullRootCover_heightOnePrime_trichotomy
        hNC i hi P hP htiP e he N hN with
    ⟨σ, hgeometryB, hn, -, hgeometryD, htrichotomy⟩
  refine ⟨σ, ⟨hgeometryD.1, hgeometryD.2.1, hgeometryD.2.2.1⟩, ?_⟩
  let R := Localization.AtPrime P
  let n := heightTwoConditionalOtherExponent t i r P e σ
  let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
  let B := iteratedRadical R d n a
  let y : R := algebraMap A R (t i)
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let : IsRegularLocalRing B := hgeometryB.1
  let : IsDomain B := hgeometryB.2.1
  let : IsRegularLocalRing D := hgeometryD.1
  let : IsDomain D := hgeometryD.2.1
  let : IsIntegrallyClosed D :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hgeometryD.2.2.1
  let : Algebra R K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsScalarTower A R K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  let : IsFractionRing R K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : Module.FaithfullyFlat R B :=
    faithfullyFlat_iteratedRadical n a hn
  let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
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
  let canonicalAK' : Algebra A K' :=
    ((algebraMap K K').comp (algebraMap A K)).toAlgebra
  let : SMul A K' := canonicalAK'.toSMul
  let : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq' rfl
  let Cnorm := integralClosure A L
  let : IsFractionRing Cnorm L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L Cnorm
  let : FaithfulSMul A Cnorm :=
    (faithfulSMul_iff_algebraMap_injective A Cnorm).mpr fun x z hxz ↦ by
      have hL := congrArg (fun c : Cnorm ↦ (c : L)) hxz
      change algebraMap A L x = algebraMap A L z at hL
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      simpa only [IsScalarTower.algebraMap_apply A K L] using hL
  intro K'target m hm Mtarget q hqPrime hqHeight
  have hcases := @htrichotomy q hqPrime hqHeight
  let M := GenericTensorFieldComponent m
  let : Algebra D M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := D) m
  let : SMul D M :=
    (genericTensorFieldComponentLeftScalarAlgebra (R := D) m).toSMul
  let : IsScalarTower D K' M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Q := Localization.AtPrime q
  let : Algebra Q K' :=
    localizationAtPrimeToFractionFieldAlgebra (K := K') q
  let : IsScalarTower D Q K' :=
    localizationAtPrimeToFractionField_isScalarTower (K := K') q
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
  rcases hcases with
    ⟨-, -, hselected | hother | haway⟩
  · exact
      localization_integralClosure_galoisFullRootCover_selectedBranch_fixedComponent_etale
        (K := K) (L := L) hNC i hi P hP htiP (hCharZero i hi) σ
          hn ⟨hgeometryD.1, hgeometryD.2.1, hgeometryD.2.2.1⟩
          m hm q hqHeight hselected
  · rcases hother with ⟨k, hkActive, htkP, -, -, hunderB⟩
    cases d with
    | zero => exact Fin.elim0 k
    | succ s =>
      exact
        localization_integralClosure_galoisFullRootCover_otherBranch_fixedComponent_etale
          (K := K) (L := L) hNC i P hP htiP σ k hkActive htkP
            (hCharZero (i.succAbove (σ k)) hkActive) hn
            ⟨hgeometryD.1, hgeometryD.2.1, hgeometryD.2.2.1⟩
            m hm q hqHeight hunderB
  · let canonicalAD : Algebra A D :=
      ((algebraMap R D).comp (algebraMap A R)).toAlgebra
    let : SMul A D := canonicalAD.toSMul
    let : IsScalarTower A R D := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower R D K' := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower A D K' := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      calc
        algebraMap A K' x = algebraMap K K' (algebraMap A K x) := rfl
        _ = algebraMap K K' (algebraMap R K (algebraMap A R x)) := by
          rw [← IsScalarTower.algebraMap_apply A R K]
        _ = algebraMap R K' (algebraMap A R x) :=
          (IsScalarTower.algebraMap_apply R K K' _).symm
        _ = algebraMap D K' (algebraMap R D (algebraMap A R x)) :=
          IsScalarTower.algebraMap_apply R D K' _
        _ = algebraMap D K' (algebraMap A D x) := by
          rw [IsScalarTower.algebraMap_apply A R D]
    have hf : f ≠ 0 :=
      (hNC.2.2.2.2.1.ne_zero_iff).mpr <| by
        rw [boundaryProduct]
        exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
          (hNC.2.2.2.1 j (Finset.mem_filter.mp hj).2).ne_zero
    have hdisjD : Disjoint
        (((Submonoid.powers (algebraMap A D f) : Submonoid D) : Set D))
        (q : Set D) := by
      rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
      intro hfq
      have hfUnder : algebraMap R B (algebraMap A R f) ∈ q.under B := by
        change algebraMap B D (algebraMap R B (algebraMap A R f)) ∈ q
        simpa only [IsScalarTower.algebraMap_apply A R D,
          IsScalarTower.algebraMap_apply R B D] using hfq
      exact ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mp haway) hfUnder
    exact
      localization_integralClosure_genericTensorFieldComponent_etale_of_awayMap
        (A := A) (C := Cnorm) (D := D) (F := K) (E := L) (K := K')
          f hf hAway q hdisjD m

end EtaleFundamentalGroups.Kummer

end
