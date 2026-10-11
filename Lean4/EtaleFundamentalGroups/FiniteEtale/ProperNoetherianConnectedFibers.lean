/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.ProperLocalScalarSections
import EtaleFundamentalGroups.FiniteEtale.ProperNoetherianNormalization
import SchemeTheory.Affine.StalkBaseChangeSections
import SchemeTheory.Affine.GeometricallyConnectedOfGlobalSections
import SchemeTheory.Morphisms.NormalizationPushforward
import SchemeTheory.Morphisms.ProperNormalization
import SchemeTheory.Morphisms.EtalePostcomposition
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Geometrically connected fibres of the actual proper normalization

The actual pushforward section isomorphism survives localization to each
target stalk and then the nonflat change to its residue field. Scalar
sections over that field imply geometric connectedness. For a proper flat
geometrically reduced family, the previously computed finite étale second
normalization map supplies flatness and geometric reducedness of the first.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A proper flat geometrically reduced family with scalar pushforward
structure sheaf has geometrically connected fibres. The fibre section
isomorphisms are constructed through stalk and residue-field base change. -/
theorem geometricallyConnected_of_proper_flat_geometricallyReduced_of_isIso_c
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyReduced f] [IsIso f.c] :
    GeometricallyConnected f := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr
  intro y
  let R : Type u := S.presheaf.stalk y
  let q : Spec (CommRingCat.of R) ⟶ S := S.fromSpecStalk y
  let fR : pullback f q ⟶ Spec (CommRingCat.of R) := pullback.snd f q
  have hSections : IsIso fR.appTop :=
    isIso_appTop_pullback_fromSpecStalk_of_isIso_c f y
  have hResidueSections :=
    isIso_appTop_baseChange_of_proper_flat_geometricallyReduced_local (R := R) fR
      (IsLocalRing.ResidueField R)
  have hResidueMap : Scheme.TwoAffineOpenCover.specMap R (IsLocalRing.ResidueField R) =
      Spec.map (S.residue y) := rfl
  rw [hResidueMap] at hResidueSections
  let fκ : pullback fR (Spec.map (S.residue y)) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField R)) :=
    pullback.snd fR (Spec.map (S.residue y))
  have hResidueQuasiCompact : QuasiCompact fκ := inferInstance
  have hResidueQuasiSeparated : QuasiSeparated fκ := inferInstance
  have hResidueIso : IsIso fκ.appTop := hResidueSections
  have hConnected : GeometricallyConnected
      (pullback.snd fR (Spec.map (S.residue y))) :=
    geometricallyConnected_of_isIso_appTop_to_field (K := IsLocalRing.ResidueField R)
      (X := pullback fR (Spec.map (S.residue y))) fκ
  let e := pullbackLeftPullbackSndIso f q (Spec.map (S.residue y))
  have hProjection : e.hom ≫ f.fiberToSpecResidueField y =
      pullback.snd fR (Spec.map (S.residue y)) :=
    pullbackLeftPullbackSndIso_hom_snd f q (Spec.map (S.residue y))
  apply ((show MorphismProperty Scheme.{u} from @GeometricallyConnected).cancel_left_of_respectsIso
    e.hom (f.fiberToSpecResidueField y)).mp
  rw [hProjection]
  exact hConnected

/-- The actual first map of relative normalization has geometrically
connected fibres for a proper flat geometrically reduced family over a
locally Noetherian base. The second map's étaleness and all section
comparisons are supplied by the proved constructions. -/
theorem geometricallyConnected_toNormalization_of_proper_flat_geometricallyReduced_noetherian
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S)
    [IsProper f] [Flat f] [GeometricallyReduced f] :
    GeometricallyConnected f.toNormalization := by
  obtain ⟨hFinite, hEtale⟩ :=
    finite_etale_fromNormalization_of_proper_flat_geometricallyReduced_noetherian f
  have hNoetherian : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have hFlat : Flat (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ (inferInstance : Flat f)
  have hPresentation : LocallyOfFinitePresentation
      (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸
      (inferInstance : LocallyOfFinitePresentation f)
  have hReduced : GeometricallyReduced (f.toNormalization ≫ f.fromNormalization) :=
    f.toNormalization_fromNormalization.symm ▸ (inferInstance : GeometricallyReduced f)
  obtain ⟨hFirstFlat, _, hFirstReduced⟩ :=
    flat_finitePresentation_geometricallyReduced_of_comp_etale
      f.toNormalization f.fromNormalization
  have hSections : IsIso f.toNormalization.c := f.isIso_toNormalization_c
  exact geometricallyConnected_of_proper_flat_geometricallyReduced_of_isIso_c
    f.toNormalization

end AlgebraicGeometry
