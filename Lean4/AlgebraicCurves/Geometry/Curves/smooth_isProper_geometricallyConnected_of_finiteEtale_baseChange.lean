/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.RingTheory.Finiteness.Descent
import AlgebraicCurves.Geometry.Schemes.Smooth_descendsAlong_surjective_inf_flat_inf_quasiCompact

/-!
# smooth is Proper geometrically Connected of finite Etale base Change
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace FiniteEtaleBaseChangeDescent
open _root_.AlgebraicGeometry

theorem locallyOfFiniteType_descendsAlong :
    MorphismProperty.DescendsAlong (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : MorphismProperty.IsStableUnderBaseChange (@LocallyOfFiniteType : MorphismProperty
    Scheme.{u}) :=
    locallyOfFiniteType_isStableUnderBaseChange
  exact HasRingHomProperty.descendsAlong_flat
    (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u})) (Q := RingHom.FiniteType)
    RingHom.FiniteType.codescendsAlong_faithfullyFlat

theorem isSeparated_iff_universallyClosed_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsSeparated f ↔ UniversallyClosed (pullback.diagonal f) := by
  refine ⟨fun _ => inferInstance, fun _ => ⟨?_⟩⟩
  exact IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal (@UniversallyClosed : MorphismProperty Scheme.{u}) :=
      by
  ext X Y f
  change IsSeparated f ↔ UniversallyClosed (pullback.diagonal f)
  exact isSeparated_iff_universallyClosed_diagonal f

theorem isSeparated_descendsAlong :
    MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : MorphismProperty.IsStableUnderBaseChange (@Surjective : MorphismProperty Scheme.{u}) := by
    refine .mk' ?_
    introv hg
    simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
    rw [hg, Set.preimage_univ]
  have : MorphismProperty.IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) :=
    Flat.isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := @Surjective) (Q := @Flat)
  have : MorphismProperty.IsStableUnderBaseChange
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf (P := @Surjective ⊓ @Flat) (Q := @QuasiCompact)
  have hbc : MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed : MorphismProperty
    Scheme.{u}) :=
    universallyClosed_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@UniversallyClosed : MorphismProperty Scheme.{u}) := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  have : MorphismProperty.DescendsAlong (@UniversallyClosed : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  have hdiag (C : Type (u + 1)) [Category.{u} C] [HasPullbacks C]
      (P Q : MorphismProperty C) [P.DescendsAlong Q] [P.RespectsIso]
      [Q.IsStableUnderBaseChange] : (MorphismProperty.diagonal P).DescendsAlong Q :=
    inferInstance
  rw [isSeparated_eq_diagonal_universallyClosed]
  exact hdiag Scheme.{u} (@UniversallyClosed : MorphismProperty Scheme.{u})
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact)


theorem isProper_descendsAlong :
    MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := isSeparated_descendsAlong.{u}
  have := locallyOfFiniteType_descendsAlong.{u}
  have : MorphismProperty.DescendsAlong (@UniversallyClosed : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact
  have : MorphismProperty.DescendsAlong (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty
    Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    MorphismProperty.DescendsAlong.inf (P := @IsSeparated) (W := @UniversallyClosed)
  rw [isProper_eq]
  exact MorphismProperty.DescendsAlong.inf
    (P := @IsSeparated ⊓ @UniversallyClosed) (W := @LocallyOfFiniteType)

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S)
  [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  have : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l')
      (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd
    b kL) sq
  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.FiniteEtaleBaseChangeDescent

open AlgebraicGeometry.FiniteEtaleBaseChangeDescent in
theorem _root_.AlgebraicGeometry.smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) {X' : Scheme.{u}} (x' : X' ⟶ Spec
      (CommRingCat.of R'))
    (hsm : Smooth x') (hpr : IsProper x') (hgc : GeometricallyConnected x')
    (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X')
    (he : e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Smooth f ∧ IsProper f ∧ GeometricallyConnected f := by
  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hfl, hsu⟩ := (flat_and_surjective_SpecMap_iff _).mpr hff
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map
    (CommRingCat.ofHom (algebraMap R R'))) :=
    ⟨⟨hsu, hfl⟩, inferInstance⟩
  have hres (P : MorphismProperty Scheme.{u}) (hbc : P.IsStableUnderBaseChange) : P.RespectsIso :=
    by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    hres (@Smooth : MorphismProperty Scheme.{u}) smooth_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    hres (@IsProper : MorphismProperty Scheme.{u}) IsProper.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    hres (@GeometricallyConnected : MorphismProperty Scheme.{u})
      (GeometricallyConnected.eq_geometrically ▸ inferInstance)
  have hsm' : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom x').mpr hsm
  have hpr' : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom x').mpr hpr
  have hgc' : GeometricallyConnected (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R
    R')))) := by
    rw [← he]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom
      x').mpr hgc
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hsu
  refine ⟨?_, ?_, ?_⟩
  · have := AlgebraicGeometry.Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hsm'
  · have := isProper_descendsAlong.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsProper)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hpr'
  · exact geometricallyConnected_of_pullback_snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))
end smooth_isProper_geometricallyConnected_of_finiteEtale_baseChange
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
