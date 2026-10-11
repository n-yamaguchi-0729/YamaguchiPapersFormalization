/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.LocalGeometry.HeightOne.BoundaryPrimeDichotomy
import EtaleFundamentalGroups.Kummer.GenericTensor.Tower.FinalNormalizationLocal
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.Prefix.ConditionalBoundaryAway
import EtaleFundamentalGroups.Kummer.NormalCrossings.Galois.FullRootCover.FixedComponentEtale
import EtaleFundamentalGroups.Purity.SpecialLocal.DimensionTwo.IntegralClosure.Local

/-!
# One permutation for the conditional and selected-root covers

The conditional root cover and the final selected-root cover must use the
same permutation of the other branches.  This file keeps the permutation
chosen by the conditional selected-away theorem, retains its regular
quotient geometry, and adjoins the selected root without making a second
choice.

For a fixed component of the final generic tensor product, its literal
contraction to the conditional generic tensor product supplies the
selected-away input.  Away from the new root, that input base-changes to the
final cover.  At the new root, the selected-branch theorem applies.  Purity
then returns etaleness of the normalization in the original literal final
component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uA uK uL

/-- The two chosen fraction-field actions induced from a common fraction
field are compatible with the canonical lift from the intermediate fraction
ring. -/
private theorem fractionFieldTower_isScalarTower_of_common_base
    {R B D : Type uA} {K : Type uK}
    [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Algebra R B]
    [CommRing D] [IsDomain D] [Algebra B D] [Algebra R D]
    [IsScalarTower R B D]
    [Field K] [algRK : Algebra R K] [IsFractionRing R K]
    [algKKB : Algebra K (FractionRing B)]
    [towerR_K_KB : IsScalarTower R K (FractionRing B)]
    [algKKD : Algebra K (FractionRing D)]
    [towerR_K_KD : IsScalarTower R K (FractionRing D)]
    [algKBKD : Algebra (FractionRing B) (FractionRing D)]
    [towerR_KB_KD : IsScalarTower R (FractionRing B) (FractionRing D)] :
    IsScalarTower K (FractionRing B) (FractionRing D) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  have hmaps :
      algebraMap K (FractionRing D) =
        (algebraMap (FractionRing B) (FractionRing D)).comp
          (algebraMap K (FractionRing B)) := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro z
    calc
      algebraMap K (FractionRing D) (algebraMap R K z) =
          algebraMap R (FractionRing D) z :=
        (IsScalarTower.algebraMap_apply R K (FractionRing D) z).symm
      _ = algebraMap (FractionRing B) (FractionRing D)
            (algebraMap R (FractionRing B) z) :=
        IsScalarTower.algebraMap_apply R (FractionRing B) (FractionRing D) z
      _ = algebraMap (FractionRing B) (FractionRing D)
            (algebraMap K (FractionRing B) (algebraMap R K z)) := by
        exact congrArg (algebraMap (FractionRing B) (FractionRing D))
          (IsScalarTower.algebraMap_apply R K (FractionRing B) z)
  exact DFunLike.congr_fun hmaps x

/-- A ring equivalence over the base of a localization is automatically
linear over the localization when both target actions extend the same base
action. -/
private noncomputable def algEquivOverLocalizationBase
    {R S U V : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing V]
    (M : Submonoid R)
    [Algebra R S] [IsLocalization M S]
    [Algebra R U] [Algebra R V]
    [Algebra S U] [Algebra S V]
    [IsScalarTower R S U] [IsScalarTower R S V]
    (e : U ≃ₐ[R] V) : U ≃ₐ[S] V :=
  { toRingEquiv := e.toRingEquiv
    commutes' := by
      intro z
      have hmaps :
          e.toRingHom.comp (algebraMap S U) = algebraMap S V := by
        apply IsLocalization.ringHom_ext M
        ext x
        change e (algebraMap S U (algebraMap R S x)) =
          algebraMap S V (algebraMap R S x)
        rw [← IsScalarTower.algebraMap_apply R S U,
          ← IsScalarTower.algebraMap_apply R S V]
        exact e.commutes x
      exact DFunLike.congr_fun hmaps z }

/-- An equivalence of algebras identifies their localizations over a base
prime.  Etaleness therefore transports over that same localized base. -/
private theorem localization_etale_of_baseAlgEquiv
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (q : Ideal R) [q.IsPrime] (e : S ≃ₐ[R] T)
    (hEtale : Algebra.Etale (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid T q.primeCompl))) :
    Algebra.Etale (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) := by
  let LS := Localization (Algebra.algebraMapSubmonoid S q.primeCompl)
  let LT := Localization (Algebra.algebraMapSubmonoid T q.primeCompl)
  let eLocR : LS ≃ₐ[R] LT :=
    IsLocalization.algEquivOfAlgEquiv
      (A := R) (R := S) (P := T)
      (M := Algebra.algebraMapSubmonoid S q.primeCompl)
      (T := Algebra.algebraMapSubmonoid T q.primeCompl) LS LT e
      (Algebra.algebraMapSubmonoid_map_eq q.primeCompl e.toAlgHom)
  let eLocQ : LS ≃ₐ[Localization.AtPrime q] LT :=
    algEquivOverLocalizationBase q.primeCompl eLocR
  exact Algebra.Etale.of_equiv eLocQ.symm

/-- The conditional selected-away theorem and the final fixed-component
purity theorem, synchronized at one literal permutation.

For every final component m, the output retains its literal contraction
n to the conditional tensor product.  Thus the selected-away statement is
about exactly the intermediate component used to prove etaleness of the
normalization in m; no component equality, right-map bijectivity, or
finrank equality is assumed. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisPrefix_selectedAway_fullRoot_fixedComponent_etale
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
      let yB : B := algebraMap R B y
      let F : B[X] := X ^ N - C yB
      let D := AdjoinRoot F
      ∃ hgeometryB : IsRegularLocalRing B ∧ IsDomain B ∧
          ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧ Prime yB ∧
          IsDomain (B ⧸ Ideal.span ({yB} : Set B)) ∧
          IsRegularLocalRing (B ⧸ Ideal.span ({yB} : Set B)),
        ∃ hgeometryD : IsRegularLocalRing D ∧ IsDomain D ∧
            ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
            Prime (AdjoinRoot.root F),
          let : IsRegularLocalRing B := hgeometryB.1
          let : IsDomain B := hgeometryB.2.1
          let : IsIntegrallyClosed B :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryB.2.2.1
          let : IsRegularLocalRing D := hgeometryD.1
          let : IsDomain D := hgeometryD.2.1
          let : IsIntegrallyClosed D :=
            SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
              hgeometryD.2.2.1
          let hn : ∀ k, 0 < n k :=
            heightTwoConditionalOtherExponent_pos_of_pos t i r P e
              (heightTwoOtherBranchGaloisRamificationIndex_pos
                (K := K) (L := L) t hNC i) σ
          let hN : 0 < N :=
            heightTwoSelectedBranchGaloisRamificationIndex_pos
              (K := K) (L := L) t hNC i
          let : Module.FaithfullyFlat R B :=
            faithfullyFlat_iteratedRadical n a hn
          let : FaithfulSMul R B := Module.FaithfullyFlat.faithfulSMul
          let : Module.FaithfullyFlat B D :=
            faithfullyFlat_adjoinRoot_X_pow_sub_C hN yB
          let : FaithfulSMul B D := Module.FaithfullyFlat.faithfulSMul
          let : FaithfulSMul R D := FaithfulSMul.trans R B D
          let : Algebra R K :=
            localizationAtPrimeToFractionFieldAlgebra (K := K) P
          let : IsFractionRing R K :=
            localizationAtPrimeToFractionField_isFractionRing (K := K) P
          let KB := FractionRing B
          let KD := FractionRing D
          let : FaithfulSMul R KB := FaithfulSMul.trans R B KB
          let : FaithfulSMul R KD := FaithfulSMul.trans R D KD
          let : FaithfulSMul B KD := FaithfulSMul.trans B D KD
          let : Algebra K KB :=
            chosenFractionFieldToFaithfulFieldAlgebra
              (R := R) (K := K) (F := KB)
          let : Algebra K KD :=
            galoisFullRootCoverFractionFieldAlgebra n a hn N hN y
          let : Algebra KB KD := FractionRing.liftAlgebra B KD
          ∃ hTower : IsScalarTower K KB KD,
            let : IsScalarTower K KB KD := hTower
            ∃ hFin : FiniteDimensional KB KD,
              let : FiniteDimensional KB KD := hFin
              ∀ (m : Ideal (KD ⊗[K] L)) (hm : m.IsMaximal),
                let : m.IsMaximal := hm
                let n₀ := genericTensorTowerIntermediateIdeal
                  (K := K) (F := KB) (F' := KD) (L := L) m
                let : n₀.IsMaximal :=
                  genericTensorTowerIntermediateIdeal_isMaximal
                    (K := K) (F := KB) (F' := KD) (L := L) m
                let M₀ := GenericTensorFieldComponent n₀
                let bM0Algebra : Algebra B M₀ :=
                  genericTensorFieldComponentLeftScalarAlgebra (R := B) n₀
                let : SMul B M₀ := bM0Algebra.toSMul
                let : IsScalarTower B KB M₀ :=
                  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
                let M := GenericTensorFieldComponent m
                let dMAlgebra : Algebra D M :=
                  genericTensorFieldComponentLeftScalarAlgebra (R := D) m
                let : SMul D M := dMAlgebra.toSMul
                let : IsScalarTower D KD M :=
                  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
                (Localization.awayMap
                    (algebraMap B (integralClosure B M₀)) yB).Etale ∧
                  Module.Finite D (integralClosure D M) ∧
                    Algebra.Etale D (integralClosure D M) := by
  classical
  intro e N
  rcases (
 splitStrictNormalCrossings_heightTwo_galoisConditionalPrefix_fixedComponent_selectedAway_etale_rich
    (K := K) (L := L) hNC i hi P hP htiP hCharZero hAway) with
    ⟨σ, hgeometryB, hprefix⟩
  refine ⟨σ, ?_⟩
  intro R n a B y yB F D
  refine ⟨hgeometryB, ?_⟩
  have hgeometryD :
      IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
        Prime (AdjoinRoot.root F) := by
    let : IsRegularLocalRing B := hgeometryB.1
    let : IsDomain B := hgeometryB.2.1
    have hfull := heightTwoPrimeRootCover_geometry
      (heightTwoSelectedBranchGaloisRamificationIndex_pos
        (K := K) (L := L) t hNC i)
      hgeometryB.2.2.2.1 hgeometryB.2.2.2.2.2 hgeometryB.2.2.1
    exact ⟨hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2.1⟩
  refine ⟨hgeometryD, ?_⟩
  intro hRegularB hDomainB hNormalB hRegularD hDomainD hNormalD hn hN
    hFlatRB hFaithRB hFlatBD hFaithBD hFaithRD aRK hFracRK KB KD
    hFaithRKB hFaithRKD hFaithBKD aKKB aKKD aKBKD
  let : IsScalarTower A R K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  let : IsScalarTower R K KB :=
    chosenFractionFieldToFaithfulField_isScalarTower
      (R := R) (K := K) (F := KB)
  let : IsScalarTower R K KD :=
    galoisFullRootCoverFractionField_isScalarTower n a hn N hN y
  let : IsScalarTower R B KB := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B D KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R D KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B KD := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B KB KD :=
    FractionRing.isScalarTower_liftAlgebra B KD
  let : IsScalarTower R KB KD := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    calc
      algebraMap R KD z = algebraMap B KD (algebraMap R B z) :=
        IsScalarTower.algebraMap_apply R B KD z
      _ = algebraMap KB KD (algebraMap B KB (algebraMap R B z)) :=
        IsScalarTower.algebraMap_apply B KB KD _
      _ = algebraMap KB KD (algebraMap R KB z) := by
        rw [IsScalarTower.algebraMap_apply R B KB]
  refine ⟨fractionFieldTower_isScalarTower_of_common_base
    (R := R) (B := B) (D := D) (K := K), ?_⟩
  intro hTower
  let : Module.Finite B D := by
    simpa only [D, F] using
      (monic_X_pow_sub_C yB hN.ne').finite_adjoinRoot
  let eGeneric : (KB ⊗[B] D) ≃ₐ[KB] KD :=
    finiteGenericFiberAlgEquiv
      (R := B) (C := D) (K := KB) (E := KD)
  let : Module.Finite KB (KB ⊗[B] D) :=
    Module.Finite.base_change B KB D
  refine ⟨Module.Finite.equiv eGeneric.toLinearEquiv, ?_⟩
  intro hFin m hm hMaxM n₀ hMaxn M₀ bM0Algebra smulBM0 towerBKBM0
    M dMAlgebra smulDM towerDKDM
  have hAwayPrefix :
      (Localization.awayMap
        (algebraMap B (integralClosure B M₀)) yB).Etale :=
    hprefix n₀ inferInstance
  have hfiniteM : Module.Finite D (integralClosure D M) :=
    SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
      (K := KD) hgeometryD.2.2.1
  refine ⟨hAwayPrefix, hfiniteM, ?_⟩
  apply
    SpecialLocalPurity.integralClosure_etale_of_isRegularLocalRing_dimension_two
      (A := D) (K := KD) (L := M) hgeometryD.2.2.1
  intro q hqPrime hqHeight
  rcases
      heightOnePrime_eq_span_or_disjoint_powers_of_associated
        hgeometryD.2.2.2 (Associated.refl (AdjoinRoot.root F)) q hqHeight with
    hselected | hrootAway
  · exact
      localization_integralClosure_galoisFullRootCover_selectedBranch_fixedComponent_etale
        (K := K) (L := L) hNC i hi P hP htiP (hCharZero i hi) σ
          hn ⟨hgeometryD.1, hgeometryD.2.1, hgeometryD.2.2.1⟩
          m hm q hqHeight hselected
  · have hrootNot : AdjoinRoot.root F ∉ q := by
      exact (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mp hrootAway
    have hyD : algebraMap B D yB ∉ q := by
      intro hyq
      apply hrootNot
      apply (inferInstance : q.IsPrime).mem_of_pow_mem N
      rw [adjoinRoot_root_pow]
      simpa only [F, D, AdjoinRoot.algebraMap_eq] using hyq
    have hyDisjoint :
        Disjoint
          (((Submonoid.powers (algebraMap B D yB) : Submonoid D) : Set D))
          (q : Set D) := by
      rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
      exact hyD
    let C₀ := integralClosure B M₀
    let : Module.Finite B C₀ :=
      SpecialLocalPurity.integralClosure_finite_of_isRegularLocalRing_dimension_two
        (K := KB) hgeometryB.2.2.1
    let : IsFractionRing C₀ M₀ :=
      IsIntegralClosure.isFractionRing_of_finite_extension B KB M₀ C₀
    let : FaithfulSMul B C₀ :=
      (faithfulSMul_iff_algebraMap_injective B C₀).mpr fun x z hxz ↦ by
        have hM₀ := congrArg (fun c : C₀ ↦ (c : M₀)) hxz
        change algebraMap B M₀ x = algebraMap B M₀ z at hM₀
        apply IsFractionRing.injective B KB
        apply (algebraMap KB M₀).injective
        simpa only [IsScalarTower.algebraMap_apply B KB M₀] using hM₀
    let q₂ := genericTensorTowerSecondIdeal
      (K := K) (F := KB) (F' := KD) (L := L) m
    let : q₂.IsMaximal :=
      genericTensorTowerSecondIdeal_isMaximal
        (K := K) (F := KB) (F' := KD) (L := L) m
    let M₂ := GenericTensorFieldComponent q₂
    let dM2Algebra : Algebra D M₂ :=
      genericTensorFieldComponentLeftScalarAlgebra (R := D) q₂
    let : SMul D M₂ := dM2Algebra.toSMul
    let : IsScalarTower D KD M₂ :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hlocal₂ :=
      localization_integralClosure_genericTensorFieldComponent_etale_of_awayMap
        (A := B) (C := C₀) (D := D)
        (F := KB) (E := M₀) (K := KD)
        yB hgeometryB.2.2.2.1.ne_zero hAwayPrefix q hyDisjoint q₂
    let CM := integralClosure D M
    let CM₂ := integralClosure D M₂
    let eIC : CM ≃ₐ[D] CM₂ :=
      genericTensorTowerFinalComponentIntegralClosureAlgEquiv
        (B := D) (K := K) (F := KB) (F' := KD) (L := L) m
    exact localization_etale_of_baseAlgEquiv (R := D) (S := CM) (T := CM₂)
      q eIC hlocal₂

end EtaleFundamentalGroups.Kummer

end
