/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The local QuasiCompact locality proof follows Mathlib's
AlgebraicGeometry/Morphisms/QuasiCompact.lean at fixed revision:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# smooth and is Separated and quasi Compact and surjective and geometrically Connected of
span eq top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnectedGluing

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PropLoc

scoped instance isZariskiLocalAtTarget_geometricallyConnected :
    IsZariskiLocalAtTarget @GeometricallyConnected :=
  GeometricallyConnected.eq_geometrically ▸ inferInstance

theorem of_span_eq_top (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      P (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f i))))))) :
    P g :=
  IsZariskiLocalAtTarget.of_openCover
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) f hf).openCover
    fun i => h i

end PropLoc

attribute [local instance] PropLoc.isZariskiLocalAtTarget_geometricallyConnected
end AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnectedGluing

namespace AlgebraicGeometry

open _root_.AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnectedGluing
universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
attribute [local instance] PropLoc.isZariskiLocalAtTarget_geometricallyConnected


theorem
 smooth_and_isSeparated_and_quasiCompact_and_surjective_and_geometricallyConnected_of_span_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    {ι : Type u} (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i : ι,
      Smooth (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f
        i)))))) ∧
      IsSeparated (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f
        i)))))) ∧
      QuasiCompact (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f
        i)))))) ∧
      Surjective (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f
        i)))))) ∧
      GeometricallyConnected (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R
        (Localization.Away (f i))))))) :
    Smooth g ∧ IsSeparated g ∧ QuasiCompact g ∧ Surjective g ∧ GeometricallyConnected g := by
  let _ : HasRingHomProperty (@Smooth : MorphismProperty Scheme.{u}) RingHom.Smooth :=
    inferInstance
  let _ : IsZariskiLocalAtTarget (@Smooth : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp (HasRingHomProperty.HasAffineProperty
      (P := (@Smooth : MorphismProperty Scheme.{u})) (Q := RingHom.Smooth))).1
  let hQuasiAffine : HasAffineProperty (@QuasiCompact : MorphismProperty Scheme.{u})
      (fun X _ _ _ => CompactSpace X) := by
    constructor
    · constructor
      · apply AffineTargetMorphismProperty.respectsIso_mk
        · intro X Y Z e _ _ H
          let _ : CompactSpace _ := H
          exact Homeomorph.compactSpace (TopCat.homeoOfIso (asIso e.inv.base))
        · intro X Y Z e _ _ H
          exact H
      · intro X Y _ f r H
        rw [Scheme.preimage_basicOpen f r]
        exact isCompact_iff_compactSpace.mp (isCompact_basicOpen _ isCompact_univ _)
      · intro X Y _ f S hS hS'
        rw [← (isAffineOpen_top _).iSup_basicOpen_eq_self_iff] at hS
        rw [← isCompact_univ_iff, ← TopologicalSpace.Opens.coe_top, ← f.preimage_top, ← hS,
          Scheme.Hom.preimage_iSup, TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk]
        exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)
    · ext X Y f
      simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
        targetAffineLocally, Subtype.forall]
      rfl
  let _ : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    (HasAffineProperty.iff.mp hQuasiAffine).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PropLoc.of_span_eq_top (P := (@Smooth : MorphismProperty Scheme.{u})) g f hf fun i =>
      (h i).1
  · exact PropLoc.of_span_eq_top (P := @IsSeparated) g f hf fun i => (h i).2.1
  · exact PropLoc.of_span_eq_top (P := (@QuasiCompact : MorphismProperty Scheme.{u})) g f hf
      fun i => (h i).2.2.1
  · exact PropLoc.of_span_eq_top (P := @Surjective) g f hf fun i => (h i).2.2.2.1
  · exact PropLoc.of_span_eq_top (P := @GeometricallyConnected) g f hf fun i => (h i).2.2.2.2
end AlgebraicGeometry
end ProofImplementation
