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
-/

import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Nyll.AlgebraicCurves.Foundations.Algebra.RingHom_QuasiFinite_codescendsAlong_faithfullyFlat

/-!
# Locally Quasi Finite descends Along surjective inf flat inf quasi Compact
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace LocallyQuasiFinite
end AlgebraicGeometry.LocallyQuasiFinite
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.LocallyQuasiFinite in
/-- Local quasi-finiteness descends along a surjective, flat, quasi-compact morphism. -/
theorem AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact' :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓
      @QuasiCompact) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) := by
    refine .mk' ?_
    introv hg
    simp only [surjective_iff, ← Set.range_eq_univ, Scheme.Pullback.range_fst] at hg ⊢
    rw [hg, Set.preimage_univ]
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h) :=
    Flat.isStableUnderBaseChange
  have : MorphismProperty.IsStableUnderBaseChange
      ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) ⊓
        (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h)) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h)
      (Q := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h)
  have : MorphismProperty.ContainsIdentities
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h) :=
    ⟨fun X => inferInstance⟩
  have : IsZariskiLocalAtSource
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h) := by
    have : HasAffineProperty (@Flat : MorphismProperty Scheme.{u}) (sourceAffineLocally
      RingHom.Flat) :=
      HasRingHomProperty.HasAffineProperty (@Flat : MorphismProperty Scheme.{u}) (Q := RingHom.Flat)
    apply HasAffineProperty.isZariskiLocalAtSource (Q := sourceAffineLocally RingHom.Flat)
    intro X Y f _ C
    have (i : C.affineRefinement.openCover.I₀) : IsAffine (C.affineRefinement.openCover.X i) :=
      Scheme.isAffine_affineOpenCover X C.affineRefinement i
    have e {X' : Scheme.{u}} (k : X' ⟶ Y) :
        (sourceAffineLocally RingHom.Flat) k ↔ Flat k :=
      (HasAffineProperty.iff_of_isAffine (P := (@Flat : MorphismProperty Scheme.{u}))
        (Q := sourceAffineLocally RingHom.Flat) (f := k)).symm
    refine (e f).trans ?_
    refine (HasRingHomProperty.iff_of_source_openCover
      (P := (@Flat : MorphismProperty Scheme.{u})) (Q := RingHom.Flat)
      (f := f) C.affineRefinement.openCover).trans ?_
    rw [show (∀ i, (sourceAffineLocally RingHom.Flat) (C.f i ≫ f)) ↔
        (∀ i, Flat (C.f i ≫ f)) from forall_congr' (fun i => e (C.f i ≫ f))]
    simp_rw [
      fun i => HasRingHomProperty.iff_of_source_openCover
        (P := (@Flat : MorphismProperty Scheme.{u}))
        (f := C.f i ≫ f) (C.X i).affineCover]
    change (∀ i : Σ j : C.I₀, (C.X j).affineCover.I₀,
      RingHom.Flat ((((C.X i.1).affineCover.f i.2 ≫ C.f i.1) ≫ f).appTop).hom) ↔
        ∀ i : C.I₀, ∀ j : (C.X i).affineCover.I₀,
          RingHom.Flat (((C.X i).affineCover.f j ≫ C.f i ≫ f).appTop).hom
    simp only [Sigma.forall, Category.assoc]
  have : MorphismProperty.IsStableUnderComposition
      ((fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) ⊓
        (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h)) := by
    refine ⟨?_⟩
    intro X Y Z h k hh hk
    have : Flat h := hh.2
    have : Flat k := hk.2
    exact ⟨⟨hk.1.surj.comp hh.1.surj⟩, Flat.comp h k⟩
  refine HasRingHomProperty.descendsAlong
    (P := (@LocallyQuasiFinite : MorphismProperty Scheme.{u}))
    (P' := (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h) ⊓
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Flat h))
    (Q := fun {R S} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R S _ _)
    (Q' := fun {R S} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _)
    (H₁ := ?_) (H₂ := ?_) RingHom.QuasiFinite.codescendsAlong_faithfullyFlat
  · intro X Y h hh
    refine ⟨hh.2, ?_⟩
    exact (IsLocalIso.le_of_isZariskiLocalAtSource
      (fun {X Y : Scheme.{u}} (k : X ⟶ Y) => Flat k)) X Y h hh.1
  · intro R S f hf
    exact (flat_and_surjective_SpecMap_iff f).mp ⟨hf.2, hf.1⟩

/-- Local quasi-finiteness descends along a surjective, flat, quasi-compact morphism. -/
theorem
  _root_.AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    DescendsAlong (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) (@Surjective ⊓ @Flat ⊓
      @QuasiCompact) :=
  AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact'
end LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
