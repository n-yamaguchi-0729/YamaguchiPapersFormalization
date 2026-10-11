/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCover
import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# Pairwise intersections in the principal cover of a punctured spectrum

This file gives the first Cech-level data for the finite principal affine
cover of a punctured local spectrum.  A pairwise intersection is identified
with the spectrum of the localization away from the product of the two
generators.  The two projections and the associated pullback functors on
finite etale covers are exposed explicitly for later descent constructions.
-/

noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

local instance finiteEtaleHasPullbacksAlongCech
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongCech
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The pairwise intersection of two members of the principal cover of the
punctured spectrum. -/
def puncturedSpectrumOverlap
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrum R).Opens :=
  puncturedSpectrumBasicOpen R i ⊓ puncturedSpectrumBasicOpen R j

/-- The corresponding ambient principal open, cut out by the product of the
two chosen generators. -/
def puncturedSpectrumAmbientOverlap
    (i j : puncturedSpectrumGeneratorIndex R) :
    (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen
    (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)

/- The ambient product basic open still avoids the closed point. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientOverlap_le
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumAmbientOverlap R i j ≤ puncturedSpectrumOpen R := by
  exact (PrimeSpectrum.basicOpen_mul_le_left
    (puncturedSpectrumGenerator R i)
    (puncturedSpectrumGenerator R j)).trans
      (puncturedSpectrumAmbientBasicOpen_le R i)

/- The intersection on the punctured spectrum is the pullback of the ambient
product basic open. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumOverlap_eq_preimage_ambient
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumOverlap R i j =
      (puncturedSpectrumOpen R).ι ⁻¹ᵁ
        puncturedSpectrumAmbientOverlap R i j := by
  change
    ((puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R i)) ⊓
      ((puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R j)) =
      (puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)
  exact ((puncturedSpectrumOpen R).ι.preimage_inf
    (U := PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R i))
    (V := PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R j))).symm.trans
      (congrArg (fun U : (Spec (.of R)).Opens => (puncturedSpectrumOpen R).ι ⁻¹ᵁ U)
        (PrimeSpectrum.basicOpen_mul (puncturedSpectrumGenerator R i)
          (puncturedSpectrumGenerator R j)).symm)

/-- The pairwise intersection is canonically the spectrum of the localization
away from the product of its two indexing generators. -/
def puncturedSpectrumOverlapIsoSpecAwayMul
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlap R i j).toScheme ≅
      Spec (.of (Localization.Away
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))) :=
  (puncturedSpectrum R).isoOfEq
      (puncturedSpectrumOverlap_eq_preimage_ambient R i j) ≪≫
    Opens.isoOfLE (puncturedSpectrumAmbientOverlap_le R i j) ≪≫
      basicOpenIsoSpecAway
        (R := .of R)
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)

/- The product-localization identification is over the ambient spectrum. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumOverlapIsoSpecAwayMul_hom_SpecMap
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlapIsoSpecAwayMul R i j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R)
          (Localization.Away
            (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) =
      (puncturedSpectrumOverlap R i j).ι ≫ puncturedSpectrumInclusion R := by
  have hbasic :
      (basicOpenIsoSpecAway
          (R := .of R)
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap R
            (Localization.Away
              (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) =
        (puncturedSpectrumAmbientOverlap R i j).ι := by
    change
      (basicOpenIsoSpecAway
          (R := CommRingCat.of R)
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R)
            (Localization.Away
              (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) = _
    simpa only [puncturedSpectrumAmbientOverlap] using
      basicOpenIsoSpecAway_hom_SpecMap
        (R := CommRingCat.of R)
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)
  let e := (puncturedSpectrum R).isoOfEq
    (puncturedSpectrumOverlap_eq_preimage_ambient R i j)
  let d := Opens.isoOfLE (puncturedSpectrumAmbientOverlap_le R i j)
  let b : (puncturedSpectrumAmbientOverlap R i j).toScheme ≅
      Spec (.of (Localization.Away
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))) :=
    basicOpenIsoSpecAway (R := .of R)
      (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)
  let m := Spec.map (CommRingCat.ofHom (algebraMap R
    (Localization.Away (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))))
  change (e.hom ≫ d.hom ≫ b.hom) ≫ m = _
  exact (Category.assoc e.hom (d.hom ≫ b.hom) m).trans
    ((congrArg (fun k => e.hom ≫ k)
      ((Category.assoc d.hom b.hom m).trans
        ((congrArg (fun k => d.hom ≫ k) hbasic).trans
          (Opens.isoOfLE_hom_ι (puncturedSpectrumAmbientOverlap_le R i j))))).trans
      ((Category.assoc e.hom
        (((puncturedSpectrumOpen R).ι ⁻¹ᵁ puncturedSpectrumAmbientOverlap R i j).ι)
        (puncturedSpectrumOpen R).ι).symm.trans
          (congrArg (fun k => k ≫ (puncturedSpectrumOpen R).ι)
            (Scheme.isoOfEq_hom_ι (puncturedSpectrum R)
              (puncturedSpectrumOverlap_eq_preimage_ambient R i j)))))

/-- The actual iterated localization: first invert the left generator and
then invert the image of the right generator. -/
abbrev puncturedSpectrumDoubleLocalization
    (i j : puncturedSpectrumGeneratorIndex R) :=
  Localization.Away
    (algebraMap R (Localization.Away (puncturedSpectrumGenerator R i))
      (puncturedSpectrumGenerator R j))

/-- Localizing at the product is canonically equivalent to the corresponding
iterated localization. -/
def puncturedSpectrumAwayMulEquivDoubleLocalization
    (i j : puncturedSpectrumGeneratorIndex R) :
    Localization.Away
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) ≃ₐ[R]
      puncturedSpectrumDoubleLocalization R i j :=
  IsLocalization.algEquiv
    (Submonoid.powers
      (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)) _ _

/-- The pairwise intersection as the spectrum of an actual iterated
localization. -/
def puncturedSpectrumOverlapIsoSpecDoubleLocalization
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlap R i j).toScheme ≅
      Spec (.of (puncturedSpectrumDoubleLocalization R i j)) :=
  puncturedSpectrumOverlapIsoSpecAwayMul R i j ≪≫
    Scheme.Spec.mapIso
      ((puncturedSpectrumAwayMulEquivDoubleLocalization R i j).toRingEquiv.symm
        |>.toCommRingCatIso.op)

/-- The inclusion of a pairwise intersection into its left chart. -/
def puncturedSpectrumOverlapToLeft
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlap R i j).toScheme ⟶
      (puncturedSpectrumBasicOpen R i).toScheme :=
  (puncturedSpectrum R).homOfLE inf_le_left

/-- The inclusion of a pairwise intersection into its right chart. -/
def puncturedSpectrumOverlapToRight
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlap R i j).toScheme ⟶
      (puncturedSpectrumBasicOpen R j).toScheme :=
  (puncturedSpectrum R).homOfLE inf_le_right

/- The affine identification of a principal chart is over the ambient
spectrum. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumBasicOpenIsoSpecAway_hom_SpecMap
    (i : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumBasicOpenIsoSpecAway R i).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Localization.Away (puncturedSpectrumGenerator R i)))) =
      (puncturedSpectrumBasicOpen R i).ι ≫ puncturedSpectrumInclusion R := by
  let d := Opens.isoOfLE (puncturedSpectrumAmbientBasicOpen_le R i)
  let b : (puncturedSpectrumAmbientBasicOpen R i).toScheme ≅
      Spec (.of (Localization.Away (puncturedSpectrumGenerator R i))) :=
    basicOpenIsoSpecAway (R := .of R) (puncturedSpectrumGenerator R i)
  let m := Spec.map (CommRingCat.ofHom
    (algebraMap R (Localization.Away (puncturedSpectrumGenerator R i))))
  change (d.hom ≫ b.hom) ≫ m = _
  exact (Category.assoc d.hom b.hom m).trans
    ((congrArg (fun k => d.hom ≫ k)
      (basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of R)
        (puncturedSpectrumGenerator R i))).trans
      (Opens.isoOfLE_hom_ι (puncturedSpectrumAmbientBasicOpen_le R i)))

/-- The canonical ring map from the left localization to the common product
localization. -/
def puncturedSpectrumAwayToOverlapLeft
    (i j : puncturedSpectrumGeneratorIndex R) :
    Localization.Away (puncturedSpectrumGenerator R i) →+*
      Localization.Away
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) :=
  IsLocalization.Away.awayToAwayRight
    (puncturedSpectrumGenerator R i) (puncturedSpectrumGenerator R j)

/-- The canonical ring map from the right localization to the common product
localization. -/
def puncturedSpectrumAwayToOverlapRight
    (i j : puncturedSpectrumGeneratorIndex R) :
    Localization.Away (puncturedSpectrumGenerator R j) →+*
      Localization.Away
        (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) :=
  IsLocalization.Away.awayToAwayLeft
    (puncturedSpectrumGenerator R j) (puncturedSpectrumGenerator R i)

/-- On affine spectra, the left projection of the Cech overlap is induced by
the canonical map to the product localization. -/
def puncturedSpectrumOverlapSpecMapLeft
    (i j : puncturedSpectrumGeneratorIndex R) :
    Spec (.of (Localization.Away
      (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))) ⟶
        Spec (.of (Localization.Away (puncturedSpectrumGenerator R i))) :=
  Spec.map (CommRingCat.ofHom (puncturedSpectrumAwayToOverlapLeft R i j))

/-- On affine spectra, the right projection of the Cech overlap is induced by
the canonical map to the product localization. -/
def puncturedSpectrumOverlapSpecMapRight
    (i j : puncturedSpectrumGeneratorIndex R) :
    Spec (.of (Localization.Away
      (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))) ⟶
        Spec (.of (Localization.Away (puncturedSpectrumGenerator R j))) :=
  Spec.map (CommRingCat.ofHom (puncturedSpectrumAwayToOverlapRight R i j))

/- The affine left projection is a morphism over `Spec R`. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumOverlapSpecMapLeft_comp_SpecMap
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumOverlapSpecMapLeft R i j ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Localization.Away (puncturedSpectrumGenerator R i)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (Localization.Away
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) := by
  simp only [puncturedSpectrumOverlapSpecMapLeft, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact IsLocalization.Away.awayToAwayRight_eq
    (puncturedSpectrumGenerator R i) (puncturedSpectrumGenerator R j) x

/- The affine right projection is a morphism over `Spec R`. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumOverlapSpecMapRight_comp_SpecMap
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumOverlapSpecMapRight R i j ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (Localization.Away (puncturedSpectrumGenerator R j)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (Localization.Away
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) := by
  simp only [puncturedSpectrumOverlapSpecMapRight, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact IsLocalization.Away.awayToAwayLeft_eq
    (puncturedSpectrumGenerator R j) (puncturedSpectrumGenerator R i) x

/- Under the affine identifications, the geometric left overlap inclusion is
exactly the spectrum map induced by the left localization map. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumOverlapIsoSpecAwayMul_hom_comp_left
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlapIsoSpecAwayMul R i j).hom ≫
        puncturedSpectrumOverlapSpecMapLeft R i j =
      puncturedSpectrumOverlapToLeft R i j ≫
        (puncturedSpectrumBasicOpenIsoSpecAway R i).hom := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R
    (Localization.Away (puncturedSpectrumGenerator R i)))))]
  simp only [Category.assoc,
    puncturedSpectrumOverlapSpecMapLeft_comp_SpecMap,
    puncturedSpectrumBasicOpenIsoSpecAway_hom_SpecMap]
  rw [puncturedSpectrumOverlapIsoSpecAwayMul_hom_SpecMap]
  change
    (puncturedSpectrumOverlap R i j).ι ≫ puncturedSpectrumInclusion R =
      ((puncturedSpectrum R).homOfLE (show
        puncturedSpectrumOverlap R i j ≤ puncturedSpectrumBasicOpen R i from
          inf_le_left) ≫
        (puncturedSpectrumBasicOpen R i).ι) ≫ puncturedSpectrumInclusion R
  rw [Scheme.homOfLE_ι]

/- Under the affine identifications, the geometric right overlap inclusion is
exactly the spectrum map induced by the right localization map. -/
omit [IsNoetherianRing R] in
@[reassoc]
theorem puncturedSpectrumOverlapIsoSpecAwayMul_hom_comp_right
    (i j : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumOverlapIsoSpecAwayMul R i j).hom ≫
        puncturedSpectrumOverlapSpecMapRight R i j =
      puncturedSpectrumOverlapToRight R i j ≫
        (puncturedSpectrumBasicOpenIsoSpecAway R j).hom := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R
    (Localization.Away (puncturedSpectrumGenerator R j)))))]
  simp only [Category.assoc,
    puncturedSpectrumOverlapSpecMapRight_comp_SpecMap,
    puncturedSpectrumBasicOpenIsoSpecAway_hom_SpecMap]
  rw [puncturedSpectrumOverlapIsoSpecAwayMul_hom_SpecMap]
  change
    (puncturedSpectrumOverlap R i j).ι ≫ puncturedSpectrumInclusion R =
      ((puncturedSpectrum R).homOfLE (show
        puncturedSpectrumOverlap R i j ≤ puncturedSpectrumBasicOpen R j from
          inf_le_right) ≫
        (puncturedSpectrumBasicOpen R j).ι) ≫ puncturedSpectrumInclusion R
  rw [Scheme.homOfLE_ι]

/- The two descriptions of the left overlap map agree after transporting
source and target through the affine identifications. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumOverlapSpecMapLeft_comp_chartIso_inv
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumOverlapSpecMapLeft R i j ≫
        (puncturedSpectrumBasicOpenIsoSpecAway R i).inv =
      (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv ≫
        puncturedSpectrumOverlapToLeft R i j := by
  rw [← cancel_epi (puncturedSpectrumOverlapIsoSpecAwayMul R i j).hom]
  rw [← Category.assoc,
    puncturedSpectrumOverlapIsoSpecAwayMul_hom_comp_left]
  simp

/- The two descriptions of the right overlap map agree after transporting
source and target through the affine identifications. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumOverlapSpecMapRight_comp_chartIso_inv
    (i j : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumOverlapSpecMapRight R i j ≫
        (puncturedSpectrumBasicOpenIsoSpecAway R j).inv =
      (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv ≫
        puncturedSpectrumOverlapToRight R i j := by
  rw [← cancel_epi (puncturedSpectrumOverlapIsoSpecAwayMul R i j).hom]
  rw [← Category.assoc,
    puncturedSpectrumOverlapIsoSpecAwayMul_hom_comp_right]
  simp

/-- Restriction of finite etale covers from the left principal chart to the
pairwise overlap. -/
def puncturedSpectrumFiniteEtaleRestrictionLeft
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale ((puncturedSpectrumBasicOpen R i).toScheme) ⥤
      FiniteEtale ((puncturedSpectrumOverlap R i j).toScheme) :=
  FiniteEtale.pullback (puncturedSpectrumOverlapToLeft R i j)

/-- Restriction of finite etale covers from the right principal chart to the
pairwise overlap. -/
def puncturedSpectrumFiniteEtaleRestrictionRight
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale ((puncturedSpectrumBasicOpen R j).toScheme) ⥤
      FiniteEtale ((puncturedSpectrumOverlap R i j).toScheme) :=
  FiniteEtale.pullback (puncturedSpectrumOverlapToRight R i j)

/-- The affine source version of restriction from the left chart. -/
def puncturedSpectrumFiniteEtaleAwayRestrictionLeft
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale
        (Spec (.of (Localization.Away (puncturedSpectrumGenerator R i)))) ⥤
      FiniteEtale
        (Spec (.of (Localization.Away
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) :=
  FiniteEtale.pullback (puncturedSpectrumOverlapSpecMapLeft R i j)

/-- The affine source version of restriction from the right chart. -/
def puncturedSpectrumFiniteEtaleAwayRestrictionRight
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale
        (Spec (.of (Localization.Away (puncturedSpectrumGenerator R j)))) ⥤
      FiniteEtale
        (Spec (.of (Localization.Away
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)))) :=
  FiniteEtale.pullback (puncturedSpectrumOverlapSpecMapRight R i j)

/-- Restriction on the geometric charts and restriction on their affine
localization models are canonically naturally isomorphic on the left. -/
def puncturedSpectrumFiniteEtaleRestrictionLeftIso
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale.pullback (puncturedSpectrumBasicOpenIsoSpecAway R i).inv ⋙
        puncturedSpectrumFiniteEtaleAwayRestrictionLeft R i j ≅
      puncturedSpectrumFiniteEtaleRestrictionLeft R i j ⋙
        FiniteEtale.pullback
          (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv := by
  change
    FiniteEtale.pullback (puncturedSpectrumBasicOpenIsoSpecAway R i).inv ⋙
        FiniteEtale.pullback (puncturedSpectrumOverlapSpecMapLeft R i j) ≅
      FiniteEtale.pullback (puncturedSpectrumOverlapToLeft R i j) ⋙
        FiniteEtale.pullback
          (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapSpecMapLeft R i j)
      (puncturedSpectrumBasicOpenIsoSpecAway R i).inv).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapSpecMapLeft_comp_chartIso_inv R i j) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv
      (puncturedSpectrumOverlapToLeft R i j)

/-- Restriction on the geometric charts and restriction on their affine
localization models are canonically naturally isomorphic on the right. -/
def puncturedSpectrumFiniteEtaleRestrictionRightIso
    (i j : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale.pullback (puncturedSpectrumBasicOpenIsoSpecAway R j).inv ⋙
        puncturedSpectrumFiniteEtaleAwayRestrictionRight R i j ≅
      puncturedSpectrumFiniteEtaleRestrictionRight R i j ⋙
        FiniteEtale.pullback
          (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv := by
  change
    FiniteEtale.pullback (puncturedSpectrumBasicOpenIsoSpecAway R j).inv ⋙
        FiniteEtale.pullback (puncturedSpectrumOverlapSpecMapRight R i j) ≅
      FiniteEtale.pullback (puncturedSpectrumOverlapToRight R i j) ⋙
        FiniteEtale.pullback
          (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapSpecMapRight R i j)
      (puncturedSpectrumBasicOpenIsoSpecAway R j).inv).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapSpecMapRight_comp_chartIso_inv R i j) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumOverlapIsoSpecAwayMul R i j).inv
      (puncturedSpectrumOverlapToRight R i j)

end AlgebraicGeometry.Scheme

end
