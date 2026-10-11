/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Away.AtUnit
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentEtale
import EtaleFundamentalGroups.FiniteEtale.Away.GenericTensor.HeightOneBaseChange
import EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.PrimeAtPrimeEquiv
import SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.HeightTwo
import EtaleFundamentalGroups.Kummer.RootCovers.Full.ActualRootLast
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.ActiveRoot.ConditionalLocalizationEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.SelectedBranchEtale
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.ConditionalRootCoverHeightOne

/-!
# The selected complement of a conditional Galois root cover

Before adjoining the selected radical, the conditional cover contains only
the roots of the other boundary branches through the chosen height-two
point.  This file proves that, in every fixed generic tensor component, the
normalization of that conditional cover is etale after the selected
parameter is inverted.

The proof globalizes literal localized-normalization statements.  A prime
avoiding the selected parameter cannot be the selected divisor.  A nonzero
such prime has height one and is either an active radical divisor, handled
after presenting the whole conditional cover as its one-root algebra, or is
on the original boundary complement.  The zero prime is included directly
in the latter case.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uD uF uM

/-- If every base-prime localization avoiding `y` has etale localized
normalization, then the literal normalization map away from `y` is etale.

The input is deliberately the localized-normalization target produced by
the height-one branch theorems.  For a prime of the global normalization,
the two canonical normalization-localization equivalences transport this
input to formal etaleness of its local ring; the etale-locus criterion then
globalizes it. -/
theorem localization_away_integralClosure_etale_of_basePrime_localizations
    {D : Type uD} {F : Type uF} {M : Type uM}
    [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [Field F] [Algebra D F] [IsFractionRing D F]
    [Field M] [Algebra F M] [Algebra D M] [IsScalarTower D F M]
    [Module.Finite D (integralClosure D M)]
    (y : D)
    (hlocal : ∀ (q : Ideal D), [q.IsPrime] → y ∉ q →
      letI := localizationAtPrimeToExtensionAlgebra
        (K := F) (L := M) q
      letI := localizationAtPrimeToExtension_isScalarTower
        (K := F) (L := M) q
      letI := integralClosureLocalizationAlgebra (L := M) q
      Algebra.Etale (Localization.AtPrime q)
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure D M) q.primeCompl))) :
    (Localization.awayMap (algebraMap D (integralClosure D M)) y).Etale := by
  let C := integralClosure D M
  let : Module.FinitePresentation D C :=
    Module.finitePresentation_of_finite D C
  let : Algebra.FinitePresentation D C :=
    Algebra.FinitePresentation.of_finitePresentation D C
  let S := Localization.Away y
  let yC : C := algebraMap D C y
  let T := Localization.Away yC
  let mapST : S →+* T := Localization.awayMap (algebraMap D C) y
  have hDT : Algebra.Etale D T := by
    apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
    intro Q hQ
    let q := Q.asIdeal.under D
    let : q.IsPrime := inferInstance
    let : Q.asIdeal.LiesOver q := inferInstance
    have hyq : y ∉ q := by
      exact (PrimeSpectrum.mem_basicOpen _ _).mp hQ
    let V := Localization.AtPrime q
    let : Algebra V M :=
      localizationAtPrimeToExtensionAlgebra (K := F) (L := M) q
    let : IsScalarTower D V M :=
      localizationAtPrimeToExtension_isScalarTower
        (K := F) (L := M) q
    let Cp := integralClosure V M
    let : Algebra C Cp := integralClosureLocalizationAlgebra (L := M) q
    let Cq := Localization
      (Algebra.algebraMapSubmonoid C q.primeCompl)
    let : Algebra.Etale V Cq := hlocal q hyq
    let eBase : Cq ≃ₐ[V] Cp :=
      localizationIntegralClosureAtPrimeAlgEquiv
        (K := F) (L := M) q
    let : Algebra.Etale V Cp := Algebra.Etale.of_equiv eBase
    let qlocal := localizedNormalizationPrime
      (K := F) (L := M) q Q.asIdeal
    let : qlocal.IsMaximal :=
      localizedNormalizationPrime_isMaximal
        (K := F) (L := M) q Q.asIdeal
    let : Algebra.FormallyEtale Cp (Localization.AtPrime qlocal) :=
      Algebra.FormallyEtale.of_isLocalization qlocal.primeCompl
    let : Algebra.FormallyEtale V (Localization.AtPrime qlocal) :=
      Algebra.FormallyEtale.comp V Cp (Localization.AtPrime qlocal)
    let : Algebra V (Localization.AtPrime Q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver q Q.asIdeal
    let ePrime : Localization.AtPrime Q.asIdeal ≃ₐ[V]
        Localization.AtPrime qlocal :=
      integralClosurePrimeLocalizationAlgEquiv
        (K := F) (L := M) q Q.asIdeal
    let : Algebra.FormallyEtale V (Localization.AtPrime Q.asIdeal) :=
      Algebra.FormallyEtale.of_equiv
        (R := V) (A := Localization.AtPrime qlocal)
        (B := Localization.AtPrime Q.asIdeal) ePrime.symm
    let : Algebra.FormallyEtale D V :=
      Algebra.FormallyEtale.of_isLocalization q.primeCompl
    change Algebra.FormallyEtale D (Localization.AtPrime Q.asIdeal)
    exact Algebra.FormallyEtale.comp D V (Localization.AtPrime Q.asIdeal)
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower D C T := inferInstance
  let : IsScalarTower D S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap D T z = mapST (algebraMap D S z)
    rw [IsScalarTower.algebraMap_apply D C T]
    simp [mapST, S, T, yC, IsLocalization.Away.map]
  let : Algebra.Etale D S := Algebra.Etale.of_isLocalizationAway y
  exact Algebra.Etale.of_restrictScalars D S T

namespace Kummer

open Polynomial
open IsLocalRing

universe uA uK uL

/-- For the conditional exact-Galois root cover at a height-two point, the
normalization in every fixed generic tensor component is etale after
inverting the selected parameter.

All geometry, active exponents, height-one alternatives, fraction-field
actions, and normalization finiteness are produced from the source chart.
In particular, no local-etaleness, component-bijectivity, or selected-root
action is a public hypothesis. -/
theorem
 splitStrictNormalCrossings_heightTwo_galoisConditionalPrefix_fixedComponent_selectedAway_etale_rich
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
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let yB : B := algebraMap R B y
      ∃ hgeometryB : IsRegularLocalRing B ∧ IsDomain B ∧
          ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB ∧
          IsDomain (B ⧸ Ideal.span ({yB} : Set B)) ∧
          IsRegularLocalRing (B ⧸ Ideal.span ({yB} : Set B)),
        let : IsRegularLocalRing B := hgeometryB.1
        let : IsDomain B := hgeometryB.2.1
        let : IsIntegrallyClosed B :=
          SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
            hgeometryB.2.2.1
        let hn : ∀ k, 0 < n k :=
          heightTwoConditionalOtherExponent_pos_of_pos t i r P e
            (heightTwoOtherBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i) σ
        let : Module.FaithfullyFlat R B :=
          faithfullyFlat_iteratedRadical n a hn
        let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
        let : Algebra R K :=
          localizationAtPrimeToFractionFieldAlgebra (K := K) P
        let : IsFractionRing R K :=
          localizationAtPrimeToFractionField_isFractionRing (K := K) P
        let K' := FractionRing B
        let : FaithfulSMul R K' := FaithfulSMul.trans R B K'
        let : Algebra K K' :=
          chosenFractionFieldToFaithfulFieldAlgebra
            (R := R) (K := K) (F := K')
        ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
          let : m.IsMaximal := hm
          let M := GenericTensorFieldComponent m
          let bMAlgebra : Algebra B M :=
            genericTensorFieldComponentLeftScalarAlgebra (R := B) m
          let : SMul B M := bMAlgebra.toSMul
          let : IsScalarTower B K' M :=
            IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
          (Localization.awayMap
            (algebraMap B (integralClosure B M)) yB).Etale := by
  classical
  intro e
  have he : ∀ k, 0 < e k :=
    heightTwoOtherBranchGaloisRamificationIndex_pos
      (K := K) (L := L) t hNC i
  rcases
      splitStrictNormalCrossings_heightTwo_conditionalRootCover_heightOnePrime_trichotomy
        hNC i hi P hP htiP e he with
    ⟨σ, hgeometry, hnSource, hdimB, htrichotomy⟩
  refine ⟨σ, ?_⟩
  intro R n a B y yB
  refine ⟨⟨hgeometry.1, hgeometry.2.1, hdimB,
    hgeometry.2.2.1, hgeometry.2.2.2.1, hgeometry.2.2.2.2⟩, ?_⟩
  intro hRegularB hDomainB hNormalB hn hFlatRB hFaithRB aRK hFracRK K' hFaithRK' aKK'
  let : IsScalarTower A R K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  let : IsScalarTower R K K' :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := R) (K := K) (F := K')
  let canonicalAB : Algebra A B :=
    ((algebraMap R B).comp (algebraMap A R)).toAlgebra
  let : SMul A B := canonicalAB.toSMul
  let : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B K' := IsScalarTower.of_algebraMap_eq' rfl
  let canonicalAK' : Algebra A K' :=
    ((algebraMap K K').comp (algebraMap A K)).toAlgebra
  let : SMul A K' := canonicalAK'.toSMul
  let : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B K' := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    calc
      algebraMap A K' x = algebraMap K K' (algebraMap A K x) := rfl
      _ = algebraMap K K' (algebraMap R K (algebraMap A R x)) := by
        rw [← IsScalarTower.algebraMap_apply A R K]
      _ = algebraMap R K' (algebraMap A R x) :=
        (IsScalarTower.algebraMap_apply R K K' _).symm
      _ = algebraMap B K' (algebraMap R B (algebraMap A R x)) :=
        IsScalarTower.algebraMap_apply R B K' _
      _ = algebraMap B K' (algebraMap A B x) := by
        rw [IsScalarTower.algebraMap_apply A R B]
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
  have hf : f ≠ 0 :=
    (hNC.2.2.2.2.1.ne_zero_iff).mpr <| by
      rw [boundaryProduct]
      exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
        (hNC.2.2.2.1 j (Finset.mem_filter.mp hj).2).ne_zero
  let hAwayTheorem :=
    localization_integralClosure_genericTensorFieldComponent_etale_of_awayMap
      (A := A) (C := Cnorm) (D := B)
      (F := K) (E := L) (K := K') f hf hAway
  intro m hm hmInstance M bMAlgebra smulBM towerBKM
  let : Module.Finite B (integralClosure B M) :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := K') hdimB
  have hfB : algebraMap A B f ≠ 0 := by
    intro hfBzero
    apply hf
    apply IsFractionRing.injective A K
    apply (algebraMap K K').injective
    calc
      algebraMap K K' (algebraMap A K f) = algebraMap A K' f :=
        (IsScalarTower.algebraMap_apply A K K' f).symm
      _ = algebraMap B K' (algebraMap A B f) :=
        IsScalarTower.algebraMap_apply A B K' f
      _ = 0 := by rw [hfBzero, map_zero]
      _ = algebraMap K K' (algebraMap A K 0) := by rw [map_zero, map_zero]
  apply localization_away_integralClosure_etale_of_basePrime_localizations
    (D := B) (F := K') (M := M) yB
  intro q hqPrime hyq
  let Q := Localization.AtPrime q
  let : Algebra Q K' :=
    localizationAtPrimeToFractionFieldAlgebra (K := K') q
  let : IsFractionRing Q K' :=
    localizationAtPrimeToFractionField_isFractionRing (K := K') q
  let qMAlgebra : Algebra Q M :=
    localizationAtPrimeToExtensionAlgebra (K := K') (L := M) q
  let : SMul Q M := qMAlgebra.toSMul
  let : IsScalarTower Q K' M :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K') (L := M) q
  let : IsScalarTower B Q M :=
    localizationAtPrimeToExtension_isScalarTower
      (K := K') (L := M) q
  let : Algebra (integralClosure B M) (integralClosure Q M) :=
    integralClosureLocalizationAlgebra (L := M) q
  have hcomplement
      (hdisj : Disjoint
        (((Submonoid.powers (algebraMap A B f) : Submonoid B) : Set B))
        (q : Set B)) :
      Algebra.Etale Q
        (Localization (Algebra.algebraMapSubmonoid
          (integralClosure B M) q.primeCompl)) := by
    have htest := hAwayTheorem q hdisj m
    dsimp only at htest
    exact htest
  by_cases hqzero : q = ⊥
  · apply hcomplement
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    rw [hqzero, Ideal.mem_bot]
    exact hfB
  have hqMaxNe : q ≠ maximalIdeal B := by
    intro hqMax
    apply hyq
    rw [hqMax]
    exact (mem_maximalIdeal yB).mpr
      (mem_nonunits_iff.mpr hgeometry.2.2.1.not_isUnit)
  have hqLt : q < maximalIdeal B :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q) hqMaxNe
  have hMaxHeight : (maximalIdeal B).height = (2 : ℕ∞) := by
    have hcast :
        (((maximalIdeal B).height : ℕ∞) : WithBot ℕ∞) =
          ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdimB]
    exact WithBot.coe_eq_coe.mp hcast
  have hqHeightLt : q.height < (2 : ℕ∞) := by
    rw [← hMaxHeight]
    exact Ideal.height_strict_mono_of_isPrime_of_isPrime hqLt
  have hqHeightLe : q.height ≤ (1 : ℕ∞) := by
    rw [← ENat.lt_add_one_iff ENat.one_ne_top, one_add_one_eq_two]
    exact hqHeightLt
  have hqHeightPos : (1 : ℕ∞) ≤ q.height :=
    Order.one_le_iff_ne_zero.mpr
      (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqzero)
  have hqHeight : q.height = 1 := le_antisymm hqHeightLe hqHeightPos
  have htriAtQ := htrichotomy q hqHeight
  rcases htriAtQ with
    hselected | hactive | hboundary
  · exfalso
    apply hyq
    rw [hselected]
    exact Ideal.mem_span_singleton_self yB
  · rcases hactive with
      ⟨k, hkActive, htkP, -, -, hq⟩
    cases d with
    | zero => exact Fin.elim0 k
    | succ s =>
      have hother : ∀ l, l ≠ k → n l = 1 :=
        heightTwoConditionalOtherExponent_eq_one_of_ne_actual
          hNC i P hP htiP e σ k hkActive htkP
      let g : R[X] := X ^ n k - C (a k)
      let Xroot := AdjoinRoot g
      let qroot := Ideal.span ({AdjoinRoot.root g} : Set Xroot)
      let singleEquiv : B ≃ₐ[R] Xroot :=
        iteratedRadicalSingleRootAlgEquiv n a k hother
      let : Algebra Xroot B := singleEquiv.symm.toRingHom.toAlgebra
      let : IsScalarTower R Xroot B := by
        apply IsScalarTower.of_algebraMap_eq
        intro z
        change algebraMap R B z = singleEquiv.symm (algebraMap R Xroot z)
        rw [← singleEquiv.commutes z, singleEquiv.symm_apply_apply]
      let : Module.Finite Xroot B :=
        Module.Finite.of_surjective (Algebra.ofId Xroot B).toLinearMap
          singleEquiv.symm.surjective
      let : FaithfulSMul Xroot B :=
        (faithfulSMul_iff_algebraMap_injective Xroot B).mpr
          singleEquiv.symm.injective
      have hroot : singleEquiv.symm (AdjoinRoot.root g) =
          iteratedRadicalRoot R n a k := by
        apply singleEquiv.injective
        rw [singleEquiv.apply_symm_apply]
        exact (iteratedRadicalSingleRootAlgEquiv_apply_root
          n a k hother).symm
      have hmap : qroot.map singleEquiv.symm.toRingHom =
          Ideal.span ({iteratedRadicalRoot R n a k} : Set B) := by
        rw [Ideal.map_span, Set.image_singleton]
        change Ideal.span ({singleEquiv.symm (AdjoinRoot.root g)} : Set B) = _
        rw [hroot]
      have hunder : q.under Xroot = qroot := by
        rw [Ideal.under_def, hq, ← hmap]
        change Ideal.comap singleEquiv.symm.toRingHom
            (Ideal.map singleEquiv.symm.toRingHom qroot) = qroot
        exact Ideal.comap_map_of_bijective _ singleEquiv.symm.bijective
      exact (
  localization_integralClosure_strictNormalCrossingsGaloisConditionalActiveRoot_fixedComponent_etale
        (K := K) (L := L) hNC i P hP σ k hkActive htkP
          (hCharZero (i.succAbove (σ k)) hkActive)
          (D := B) q hunder m hm)
  · apply hcomplement
    simpa only [IsScalarTower.algebraMap_apply A R B] using hboundary

/-- The stable public form of the conditional-prefix selected-away theorem.

The richer source theorem above additionally retains the regular quotient
geometry needed to adjoin the selected root with the same permutation. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisConditionalPrefix_fixedComponent_selectedAway_etale
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
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let yB : B := algebraMap R B y
      ∃ hgeometryB : IsRegularLocalRing B ∧ IsDomain B ∧
          ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB,
        letI : IsRegularLocalRing B := hgeometryB.1
        letI : IsDomain B := hgeometryB.2.1
        letI : IsIntegrallyClosed B :=
          SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
            hgeometryB.2.2.1
        let hn : ∀ k, 0 < n k :=
          heightTwoConditionalOtherExponent_pos_of_pos t i r P e
            (heightTwoOtherBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i) σ
        letI : Module.FaithfullyFlat R B :=
          faithfullyFlat_iteratedRadical n a hn
        letI : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
        letI : Algebra R K :=
          localizationAtPrimeToFractionFieldAlgebra (K := K) P
        letI : IsFractionRing R K :=
          localizationAtPrimeToFractionField_isFractionRing (K := K) P
        let K' := FractionRing B
        letI : FaithfulSMul R K' := FaithfulSMul.trans R B K'
        letI : Algebra K K' :=
          chosenFractionFieldToFaithfulFieldAlgebra
            (R := R) (K := K) (F := K')
        ∀ (m : Ideal (K' ⊗[K] L)) (hm : m.IsMaximal),
          letI : m.IsMaximal := hm
          let M := GenericTensorFieldComponent m
          letI : Algebra B M :=
            genericTensorFieldComponentLeftScalarAlgebra (R := B) m
          letI : SMul B M :=
            (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul
          letI : IsScalarTower B K' M :=
            IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
          (Localization.awayMap
            (algebraMap B (integralClosure B M)) yB).Etale := by
  rcases (
 splitStrictNormalCrossings_heightTwo_galoisConditionalPrefix_fixedComponent_selectedAway_etale_rich
    (K := K) (L := L) hNC i hi P hP htiP hCharZero hAway) with
    ⟨σ, hgeometryB, hcomponents⟩
  refine ⟨σ, ⟨hgeometryB.1, hgeometryB.2.1, hgeometryB.2.2.1,
    hgeometryB.2.2.2.1⟩, ?_⟩
  simpa only using hcomponents

end Kummer

end EtaleFundamentalGroups

end
