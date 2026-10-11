/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponent
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticComplementCover

/-!
# Covers on normal-crossings chart complements
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleFundamentalGroups TopologicalSpace
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X Y : Scheme.{u}}

/-- The restriction of a chart morphism to the complement of a pulled-back
ideal. -/
def comapSupportComplementTo
    (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).supportComplement.toScheme ⟶
      I.supportComplement.toScheme :=
  (Y.isoOfEq (supportComplement_comap I f)).hom ≫
    (f ∣_ I.supportComplement)

@[reassoc]
theorem comapSupportComplementTo_comp_ι
    (I : X.IdealSheafData) (f : Y ⟶ X) :
    comapSupportComplementTo I f ≫ I.supportComplement.ι =
      (I.comap f).supportComplement.ι ≫ f := by
  simp only [comapSupportComplementTo, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc]

instance (I : X.IdealSheafData) (f : Y ⟶ X) [Etale f] :
    Etale (comapSupportComplementTo I f) := by
  dsimp only [comapSupportComplementTo]
  infer_instance

private theorem boundaryProduct_ne_zero_of_splitStrictNormalCrossings
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r) :
    boundaryProduct t r ≠ 0 := by
  apply (hNC.2.2.2.2.1.ne_zero_iff).mpr
  rw [boundaryProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j hj ↦
    (hNC.2.2.2.1 j (Finset.mem_filter.mp hj).2).ne_zero

/-- Restrict a finite-etale cover to the support complement in a chart. -/
def pullbackSupportComplementCoverToChart
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (W : FiniteEtale I.supportComplement) :
    FiniteEtale (I.comap f).supportComplement :=
  (FiniteEtale.pullback (comapSupportComplementTo I f)).obj W

/-- The map from a split local boundary-away chart to the original support
complement. -/
def boundaryAwayToSupportComplement
    (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : PrimeSpectrum (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r}) :
    Spec (.of (Localization.Away (boundaryProduct t r))) ⟶
      I.supportComplement :=
  localizationAwayToSupportComplement
      (I.comap f) y P.asIdeal (boundaryProduct t r) hboundary ≫
    comapSupportComplementTo I f

/-- First restrict to the chart complement and then to its split local
boundary-away chart. -/
def pullbackSupportComplementCoverToChartBoundaryAway
    (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : PrimeSpectrum (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (W : FiniteEtale I.supportComplement) :
    FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r)))) :=
  pullbackSupportComplementCoverToBoundaryAway
    (I.comap f) y P t hboundary
      (pullbackSupportComplementCoverToChart I f W)

/-- Pullback along the composite boundary-away map agrees with successive
pullback through the chart complement. -/
def boundaryAwayPullbackCompIso
    (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : PrimeSpectrum (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (W : FiniteEtale I.supportComplement) :
    (FiniteEtale.pullback
      (boundaryAwayToSupportComplement I f y P t hboundary)).obj W ≅
      pullbackSupportComplementCoverToChartBoundaryAway
        I f y P t hboundary W := by
  let : ∀ {S T : Scheme.{u}} (g : S ⟶ T),
      MorphismProperty.IsStableUnderBaseChangeAlong
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) g :=
    fun _ ↦ ⟨fun h hg ↦ MorphismProperty.of_isPullback
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hg⟩
  let : ∀ {S T : Scheme.{u}} (g : S ⟶ T),
      MorphismProperty.HasPullbacksAlong
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) g :=
    fun _ ↦ ⟨fun _ _ ↦ inferInstance⟩
  letI (S : Scheme.{u}) : Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u})
      (⊤ : MorphismProperty Scheme.{u}) S) := FiniteEtale.instCategory S
  exact (MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤)
    (localizationAwayToSupportComplement
      (I.comap f) y P.asIdeal (boundaryProduct t r) hboundary)
    (comapSupportComplementTo I f)).app W

/-- Successive pullback of a connected Galois cover to an etale
normal-crossings chart and then to a split boundary-away chart has a pointed
connected component which is again Galois. -/
theorem exists_galoisComponent_pullbackSupportComplementCoverToBoundaryAway
    [IsIntegral X]
    (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)
    (P : PrimeSpectrum (Y.presheaf.stalk y)) {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal y).map
          (algebraMap (Y.presheaf.stalk y)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal)) :
    letI : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
    let hf := boundaryProduct_ne_zero_of_splitStrictNormalCrossings hNC
    letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
      IsLocalization.Away.isDomain
        (Localization.Away (boundaryProduct t r)) hf
    let j := localizationAwayToSupportComplement
      (I.comap f) y P.asIdeal (boundaryProduct t r) hboundary
    let g := comapSupportComplementTo I f
    letI : Nonempty (I.comap f).supportComplement :=
      ⟨j (genericPoint
        (Spec (.of (Localization.Away (boundaryProduct t r)))))⟩
    letI : Nonempty I.supportComplement :=
      ⟨g (Classical.choice
        (inferInstance : Nonempty (I.comap f).supportComplement))⟩
    ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
      ∃ (Z : FiniteEtale
          (Spec (.of (Localization.Away (boundaryProduct t r)))))
        (i : Z ⟶ pullbackSupportComplementCoverToChartBoundaryAway
          I f y P t hboundary W),
        IsGalois Z ∧ Mono i := by
  dsimp only
  let S := Localization.Away (boundaryProduct t r)
  have hf : boundaryProduct t r ≠ 0 :=
    boundaryProduct_ne_zero_of_splitStrictNormalCrossings hNC
  let : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let j := localizationAwayToSupportComplement
    (I.comap f) y P.asIdeal (boundaryProduct t r) hboundary
  let g := comapSupportComplementTo I f
  let c := boundaryAwayToSupportComplement I f y P t hboundary
  let : Nonempty (I.comap f).supportComplement :=
    ⟨j (genericPoint (Spec (.of S)))⟩
  let : Nonempty I.supportComplement :=
    ⟨g (Classical.choice
      (inferInstance : Nonempty (I.comap f).supportComplement))⟩
  let : IsIntegral I.supportComplement :=
    isIntegral_of_isOpenImmersion I.supportComplement.ι
  intro W hW
  let s : Spec (.of S) := genericPoint (Spec (.of S))
  let Omega := AlgebraicClosure ((Spec (.of S)).residueField s)
  let xi : Spec (.of Omega) ⟶ Spec (.of S) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec (.of S)).residueField s) Omega)) ≫
      (Spec (.of S)).fromSpecResidueField s
  let : IsGalois W := hW
  let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
    Classical.choice
      (nonempty_fiber_of_isConnected (FiniteEtale.fiber (xi ≫ c)) W)
  obtain ⟨Z, i, _, _, hZ, hi⟩ :=
    FiniteEtale.exists_galoisComponent_pullback c xi W hW w
  let e := boundaryAwayPullbackCompIso I f y P t hboundary W
  let i' : Z ⟶ pullbackSupportComplementCoverToChartBoundaryAway
      I f y P t hboundary W := i ≫ e.hom
  have hi' : Mono i' := by
    dsimp only [i']
    infer_instance
  exact ⟨Z, i', hZ, hi'⟩

/-- A normal-crossings point supplies an etale strict chart on which every
later split boundary-away localization has Galois connected components after
pulling back a global Galois cover. -/
theorem IsNormalCrossingsAt.exists_etaleStrictChart_galoisComponent_boundaryAway
    [IsIntegral X]
    {I : X.IdealSheafData} {x : X}
    (hI : I.IsNormalCrossingsAt x) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (I.comap f).IsStrictNormalCrossings ∧
        ∀ (P : PrimeSpectrum (U.presheaf.stalk u)) {r : ℕ}
          (t : Fin 2 → Localization.AtPrime P.asIdeal)
          (hboundary :
            ((I.comap f).stalkIdeal u).map
                (algebraMap (U.presheaf.stalk u)
                  (Localization.AtPrime P.asIdeal)) =
              Ideal.span {boundaryProduct t r})
          (hNC : IsSplitStrictNormalCrossingsAt
            (boundaryProduct t r) t r)
          (hVdomain : IsDomain (Localization.AtPrime P.asIdeal)),
          letI : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
          let hf := boundaryProduct_ne_zero_of_splitStrictNormalCrossings hNC
          letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
            IsLocalization.Away.isDomain
              (Localization.Away (boundaryProduct t r)) hf
          let j := localizationAwayToSupportComplement
            (I.comap f) u P.asIdeal (boundaryProduct t r) hboundary
          let g := comapSupportComplementTo I f
          letI : Nonempty (I.comap f).supportComplement :=
            ⟨j (genericPoint
              (Spec (.of (Localization.Away (boundaryProduct t r)))))⟩
          letI : Nonempty I.supportComplement :=
            ⟨g (Classical.choice
              (inferInstance : Nonempty (I.comap f).supportComplement))⟩
          ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
            ∃ (Z : FiniteEtale
                (Spec (.of (Localization.Away (boundaryProduct t r)))))
              (i : Z ⟶ pullbackSupportComplementCoverToChartBoundaryAway
                I f u P t hboundary W),
              IsGalois Z ∧ Mono i := by
  obtain ⟨U, f, u, hf, hfu, hstrict⟩ := hI
  refine ⟨U, f, u, hf, hfu, hstrict, ?_⟩
  intro P r t hboundary hNC hVdomain
  exact exists_galoisComponent_pullbackSupportComplementCoverToBoundaryAway
    I f u P t hboundary hNC hVdomain

end AlgebraicGeometry.Scheme.IdealSheafData

end
