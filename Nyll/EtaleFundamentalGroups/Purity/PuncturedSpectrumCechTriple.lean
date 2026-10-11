/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCech

/-!
# Triple intersections in the principal cover of a punctured spectrum

This file constructs the triple-intersection level of the principal Cech
cover.  It identifies a triple intersection with the spectrum of both the
product localization and the corresponding three-stage localization, exposes
the three maps to pairwise intersections, and records the natural
isomorphisms needed for the finite-etale cocycle condition.
-/

noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

local instance finiteEtaleHasPullbacksAlongCechTriple
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongCechTriple
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The intersection of three principal charts of the punctured spectrum. -/
def puncturedSpectrumTripleOverlap
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrum R).Opens :=
  puncturedSpectrumOverlap R i j ⊓ puncturedSpectrumBasicOpen R k

/-- The ambient basic open belonging to the product of three chosen
generators. -/
def puncturedSpectrumAmbientTripleOverlap
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (Spec (.of R)).Opens :=
  PrimeSpectrum.basicOpen
    ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
      puncturedSpectrumGenerator R k)

/- The ambient triple-product basic open avoids the closed point. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumAmbientTripleOverlap_le
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumAmbientTripleOverlap R i j k ≤
      puncturedSpectrumOpen R := by
  exact (PrimeSpectrum.basicOpen_mul_le_left
    (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)
    (puncturedSpectrumGenerator R k)).trans
      (puncturedSpectrumAmbientOverlap_le R i j)

/- The triple intersection is the pullback of the ambient triple-product
basic open. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumTripleOverlap_eq_preimage_ambient
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumTripleOverlap R i j k =
      (puncturedSpectrumOpen R).ι ⁻¹ᵁ
        puncturedSpectrumAmbientTripleOverlap R i j k := by
  rw [puncturedSpectrumTripleOverlap,
    puncturedSpectrumOverlap_eq_preimage_ambient]
  change
    ((puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)) ⊓
      ((puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R k)) =
      (puncturedSpectrumOpen R).ι ⁻¹ᵁ
        PrimeSpectrum.basicOpen
          ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
            puncturedSpectrumGenerator R k)
  exact ((puncturedSpectrumOpen R).ι.preimage_inf
    (U := PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j))
    (V := PrimeSpectrum.basicOpen (puncturedSpectrumGenerator R k))).symm.trans
      (congrArg (fun U : (Spec (.of R)).Opens => (puncturedSpectrumOpen R).ι ⁻¹ᵁ U)
        (PrimeSpectrum.basicOpen_mul
          (puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j)
          (puncturedSpectrumGenerator R k)).symm)

/-- A triple intersection is canonically the spectrum of the localization
away from the product of its three generators. -/
def puncturedSpectrumTripleOverlapIsoSpecAwayMul
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumTripleOverlap R i j k).toScheme ≅
      Spec (.of (Localization.Away
        ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
          puncturedSpectrumGenerator R k))) :=
  (puncturedSpectrum R).isoOfEq
      (puncturedSpectrumTripleOverlap_eq_preimage_ambient R i j k) ≪≫
    Opens.isoOfLE (puncturedSpectrumAmbientTripleOverlap_le R i j k) ≪≫
      basicOpenIsoSpecAway
        (R := .of R)
        ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
          puncturedSpectrumGenerator R k)

/-- The actual three-stage localization: first invert `i`, then `j`, and
finally the image of `k`. -/
abbrev puncturedSpectrumTripleLocalization
    (i j k : puncturedSpectrumGeneratorIndex R) :=
  Localization.Away
    (algebraMap R (puncturedSpectrumDoubleLocalization R i j)
      (puncturedSpectrumGenerator R k))

/-- Localization at the triple product is canonically equivalent to the
corresponding three-stage localization. -/
def puncturedSpectrumAwayTripleEquivTripleLocalization
    (i j k : puncturedSpectrumGeneratorIndex R) :
    Localization.Away
        ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
          puncturedSpectrumGenerator R k) ≃ₐ[R]
      puncturedSpectrumTripleLocalization R i j k :=
  IsLocalization.algEquiv
    (Submonoid.powers
      ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
        puncturedSpectrumGenerator R k))
    (Localization.Away
      ((puncturedSpectrumGenerator R i * puncturedSpectrumGenerator R j) *
        puncturedSpectrumGenerator R k))
    (puncturedSpectrumTripleLocalization R i j k)

/-- The triple intersection as the spectrum of an actual three-stage
localization. -/
def puncturedSpectrumTripleOverlapIsoSpecTripleLocalization
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumTripleOverlap R i j k).toScheme ≅
      Spec (.of (puncturedSpectrumTripleLocalization R i j k)) :=
  puncturedSpectrumTripleOverlapIsoSpecAwayMul R i j k ≪≫
    Scheme.Spec.mapIso
      ((puncturedSpectrumAwayTripleEquivTripleLocalization R i j k).toRingEquiv.symm
        |>.toCommRingCatIso.op)

/-- The triple intersection maps to the `(i,j)` pairwise intersection. -/
def puncturedSpectrumTripleOverlapToIJ
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumTripleOverlap R i j k).toScheme ⟶
      (puncturedSpectrumOverlap R i j).toScheme :=
  (puncturedSpectrum R).homOfLE inf_le_left

/-- The triple intersection maps to the `(i,k)` pairwise intersection. -/
def puncturedSpectrumTripleOverlapToIK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumTripleOverlap R i j k).toScheme ⟶
      (puncturedSpectrumOverlap R i k).toScheme :=
  (puncturedSpectrum R).homOfLE <|
    le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- The triple intersection maps to the `(j,k)` pairwise intersection. -/
def puncturedSpectrumTripleOverlapToJK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    (puncturedSpectrumTripleOverlap R i j k).toScheme ⟶
      (puncturedSpectrumOverlap R j k).toScheme :=
  (puncturedSpectrum R).homOfLE <|
    le_inf (inf_le_left.trans inf_le_right) inf_le_right

/- The two routes from the triple intersection to chart `i` coincide. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumTripleOverlap_comp_toChartI
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumTripleOverlapToIJ R i j k ≫
        puncturedSpectrumOverlapToLeft R i j =
      puncturedSpectrumTripleOverlapToIK R i j k ≫
        puncturedSpectrumOverlapToLeft R i k := by
  exact (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
    (U := puncturedSpectrumTripleOverlap R i j k)
    (V := puncturedSpectrumOverlap R i j)
    (W := puncturedSpectrumBasicOpen R i) inf_le_left inf_le_left).trans
      (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
        (U := puncturedSpectrumTripleOverlap R i j k)
        (V := puncturedSpectrumOverlap R i k)
        (W := puncturedSpectrumBasicOpen R i) (le_inf (inf_le_left.trans inf_le_left)
          inf_le_right) inf_le_left).symm

/- The two routes from the triple intersection to chart `j` coincide. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumTripleOverlap_comp_toChartJ
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumTripleOverlapToIJ R i j k ≫
        puncturedSpectrumOverlapToRight R i j =
      puncturedSpectrumTripleOverlapToJK R i j k ≫
        puncturedSpectrumOverlapToLeft R j k := by
  exact (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
    (U := puncturedSpectrumTripleOverlap R i j k)
    (V := puncturedSpectrumOverlap R i j)
    (W := puncturedSpectrumBasicOpen R j) inf_le_left inf_le_right).trans
      (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
        (U := puncturedSpectrumTripleOverlap R i j k)
        (V := puncturedSpectrumOverlap R j k)
        (W := puncturedSpectrumBasicOpen R j) (le_inf (inf_le_left.trans inf_le_right)
          inf_le_right) inf_le_left).symm

/- The two routes from the triple intersection to chart `k` coincide. -/
omit [IsNoetherianRing R] in
theorem puncturedSpectrumTripleOverlap_comp_toChartK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumTripleOverlapToIK R i j k ≫
        puncturedSpectrumOverlapToRight R i k =
      puncturedSpectrumTripleOverlapToJK R i j k ≫
        puncturedSpectrumOverlapToRight R j k := by
  exact (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
    (U := puncturedSpectrumTripleOverlap R i j k)
    (V := puncturedSpectrumOverlap R i k)
    (W := puncturedSpectrumBasicOpen R k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      inf_le_right).trans
      (Scheme.homOfLE_homOfLE (puncturedSpectrum R)
        (U := puncturedSpectrumTripleOverlap R i j k)
        (V := puncturedSpectrumOverlap R j k)
        (W := puncturedSpectrumBasicOpen R k) (le_inf (inf_le_left.trans inf_le_right)
          inf_le_right) inf_le_right).symm

/-- Restriction of finite-etale covers from the `(i,j)` overlap to the triple
intersection. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionIJ
    (i j k : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale ((puncturedSpectrumOverlap R i j).toScheme) ⥤
      FiniteEtale ((puncturedSpectrumTripleOverlap R i j k).toScheme) :=
  FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIJ R i j k)

/-- Restriction of finite-etale covers from the `(i,k)` overlap to the triple
intersection. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionIK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale ((puncturedSpectrumOverlap R i k).toScheme) ⥤
      FiniteEtale ((puncturedSpectrumTripleOverlap R i j k).toScheme) :=
  FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIK R i j k)

/-- Restriction of finite-etale covers from the `(j,k)` overlap to the triple
intersection. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionJK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    FiniteEtale ((puncturedSpectrumOverlap R j k).toScheme) ⥤
      FiniteEtale ((puncturedSpectrumTripleOverlap R i j k).toScheme) :=
  FiniteEtale.pullback (puncturedSpectrumTripleOverlapToJK R i j k)

/-- The two finite-etale restriction routes from chart `i` to the triple
intersection are naturally isomorphic. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionIsoI
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumFiniteEtaleRestrictionLeft R i j ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionIJ R i j k ≅
      puncturedSpectrumFiniteEtaleRestrictionLeft R i k ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionIK R i j k := by
  change
    FiniteEtale.pullback (puncturedSpectrumOverlapToLeft R i j) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIJ R i j k) ≅
      FiniteEtale.pullback (puncturedSpectrumOverlapToLeft R i k) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIK R i j k)
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToIJ R i j k)
      (puncturedSpectrumOverlapToLeft R i j)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlap_comp_toChartI R i j k) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToIK R i j k)
      (puncturedSpectrumOverlapToLeft R i k)

/-- The two finite-etale restriction routes from chart `j` to the triple
intersection are naturally isomorphic. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionIsoJ
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumFiniteEtaleRestrictionRight R i j ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionIJ R i j k ≅
      puncturedSpectrumFiniteEtaleRestrictionLeft R j k ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionJK R i j k := by
  change
    FiniteEtale.pullback (puncturedSpectrumOverlapToRight R i j) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIJ R i j k) ≅
      FiniteEtale.pullback (puncturedSpectrumOverlapToLeft R j k) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToJK R i j k)
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToIJ R i j k)
      (puncturedSpectrumOverlapToRight R i j)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlap_comp_toChartJ R i j k) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToJK R i j k)
      (puncturedSpectrumOverlapToLeft R j k)

/-- The two finite-etale restriction routes from chart `k` to the triple
intersection are naturally isomorphic. -/
def puncturedSpectrumFiniteEtaleTripleRestrictionIsoK
    (i j k : puncturedSpectrumGeneratorIndex R) :
    puncturedSpectrumFiniteEtaleRestrictionRight R i k ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionIK R i j k ≅
      puncturedSpectrumFiniteEtaleRestrictionRight R j k ⋙
        puncturedSpectrumFiniteEtaleTripleRestrictionJK R i j k := by
  change
    FiniteEtale.pullback (puncturedSpectrumOverlapToRight R i k) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToIK R i j k) ≅
      FiniteEtale.pullback (puncturedSpectrumOverlapToRight R j k) ⋙
        FiniteEtale.pullback (puncturedSpectrumTripleOverlapToJK R i j k)
  exact
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToIK R i j k)
      (puncturedSpectrumOverlapToRight R i k)).symm ≪≫
    MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlap_comp_toChartK R i j k) ≪≫
    MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤)
      (puncturedSpectrumTripleOverlapToJK R i j k)
      (puncturedSpectrumOverlapToRight R j k)

end AlgebraicGeometry.Scheme

end
