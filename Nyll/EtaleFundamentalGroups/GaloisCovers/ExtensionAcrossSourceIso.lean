/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenImmersionPullbackModel
import Nyll.SchemeTheory.Affine.Over

/-!
# Transporting finite-etale extensions across a source isomorphism

An extension problem is unchanged when its source is replaced by an
isomorphic scheme.  This file records the comparison at the level of actual
finite-etale objects and actual pullback isomorphisms.
-/

noncomputable section


open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteEtaleOverCategorySourceIso (S : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ S) :=
  inferInstanceAs (Category (FiniteEtale S))

local instance finiteEtaleHasPullbacksAlongSourceIso
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongSourceIso
    {S T : Scheme.{u}} (f : S ⟶ T) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

namespace OpenNormalPullbackModel

variable {Y : Scheme.{u}} [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- The canonical identification of a pullback component with the pulled
boundary complement, with the isomorphism to the whole pullback made explicit
so that its structural equation is definitionally visible. -/
noncomputable def sourceIsoPulledSupportComplementOver
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) [ConnectedSpace I.supportComplement]
    [Nonempty I.supportComplement]
    (xi : Spec (.of Omega) ⟶ I.supportComplement)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ I.supportComplement.ι))
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    M.sourceScheme ≅ (I.comap M.targetCover.hom).supportComplement := by
  letI : IsIso M.inclusion := M.inclusion_isIso_of_isOpenImmersion
  letI hinclusionHom : IsIso M.inclusion.hom :=
    (FiniteEtale.forget (I.supportComplement : Scheme.{u})).map_isIso M.inclusion
  letI hinclusionLeft : IsIso M.inclusion.left :=
    @Functor.map_isIso _ _ _ _ _ _
      (CategoryTheory.Over.forget (I.supportComplement : Scheme.{u}))
      M.inclusion.hom hinclusionHom
  exact asIso M.inclusion.left ≪≫ pullbackSupportComplementIso I M.targetCover

/-- The explicit component/complement identification is over the ambient
target cover. -/
@[reassoc]
theorem sourceIsoPulledSupportComplementOver_hom_comp_ι
    [IsIntegral Y] [IsNormalIntegral Y] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) [ConnectedSpace I.supportComplement]
    [Nonempty I.supportComplement]
    (xi : Spec (.of Omega) ⟶ I.supportComplement)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ I.supportComplement.ι))
    (M : OpenNormalPullbackModel I.supportComplement.ι xi U) :
    (M.sourceIsoPulledSupportComplementOver I xi U).hom ≫
        (I.comap M.targetCover.hom).supportComplement.ι =
      M.hom := by
  let : IsIso M.inclusion := M.inclusion_isIso_of_isOpenImmersion
  let hinclusionHom : IsIso M.inclusion.hom :=
    (FiniteEtale.forget (I.supportComplement : Scheme.{u})).map_isIso M.inclusion
  let hinclusionLeft : IsIso M.inclusion.left :=
    @Functor.map_isIso _ _ _ _ _ _
      (CategoryTheory.Over.forget (I.supportComplement : Scheme.{u}))
      M.inclusion.hom hinclusionHom
  change
    ((asIso M.inclusion.left ≪≫
      pullbackSupportComplementIso I M.targetCover).hom ≫
        (I.comap M.targetCover.hom).supportComplement.ι) = M.hom
  have hopen :
      (pullbackSupportComplementIso I M.targetCover).hom ≫
          (I.comap M.targetCover.hom).supportComplement.ι =
        Limits.pullback.fst M.targetCover.hom I.supportComplement.ι := by
    change
      (pullbackRestrictIsoRestrict M.targetCover.hom I.supportComplement).hom ≫
        (M.targetCover.left.isoOfEq
          (I.supportComplement_comap M.targetCover.hom).symm).hom ≫
          (I.comap M.targetCover.hom).supportComplement.ι =
        Limits.pullback.fst M.targetCover.hom I.supportComplement.ι
    have hlast := Scheme.isoOfEq_hom_ι M.targetCover.left
      (I.supportComplement_comap M.targetCover.hom).symm
    exact
      (congrArg
        (fun k =>
          (pullbackRestrictIsoRestrict
            M.targetCover.hom I.supportComplement).hom ≫ k)
        hlast).trans
          (pullbackRestrictIsoRestrict_hom_ι _ _)
  simp only [Iso.trans_hom, asIso_hom, hom, Category.assoc]
  rw [hopen]

end OpenNormalPullbackModel

/-- If `f` is identified with `e.hom ≫ j`, an extension after transporting
the source cover along `e` gives an extension along `f` itself. -/
noncomputable def extensionOfSourceIso
    {X X' Y : Scheme.{u}}
    (e : X ≅ X') (j : X' ⟶ Y) (f : X ⟶ Y)
    (h : e.hom ≫ j = f)
    (W : FiniteEtale X)
    (extension :
      Σ Z : FiniteEtale Y,
        (pullback j).obj Z ≅
          (pullback e.inv).obj W) :
    Σ Z : FiniteEtale Y, (pullback f).obj Z ≅ W := by
  let E := MorphismProperty.Over.pullbackIso @IsFiniteEtale ⊤ e
  refine ⟨extension.1, ?_⟩
  exact
    ((MorphismProperty.Over.pullbackCongr
      (P := @IsFiniteEtale) (Q := ⊤) h.symm).app extension.1) ≪≫
      ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) e.hom j).app extension.1) ≪≫
      (pullback e.hom).mapIso extension.2 ≪≫
      (E.unitIso.app W).symm

end AlgebraicGeometry.FiniteEtale
