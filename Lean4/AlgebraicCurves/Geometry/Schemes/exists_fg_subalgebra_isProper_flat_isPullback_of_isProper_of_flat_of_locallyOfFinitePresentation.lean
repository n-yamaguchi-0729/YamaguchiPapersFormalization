/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_fg_subalgebra_isProper_flat_isPullback_of_isProper_of_flat_of_locallyOfFinitePresentation.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import AlgebraicCurves.Geometry.Schemes.IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd
import AlgebraicCurves.Geometry.Schemes.Flat_exists_fg_subalgebra_of_flat_pullback_snd
import AlgebraicCurves.Geometry.Schemes.IsProper_exists_fg_subalgebra_of_isProper_pullback_snd

/-!
# exists fg subalgebra is Proper flat is Pullback of is Proper of flat of locally Of Finite
Presentation
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent
attribute [-instance] IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial
attribute [-simp] IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ApproxAux

lemma iff_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso] {X X₁ Y B : Scheme.{u}}
    {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι : Y ⟶ B} (sq : IsPullback π g f ι) :
    P (pullback.snd f ι) ↔ P g := by
  rw [← sq.isoPullback_hom_snd, P.cancel_left_of_respectsIso]

lemma exists_isPullback_of_fac {X X₁ Y B B' : Scheme.{u}} {π : X ⟶ X₁} {g : X ⟶ Y} {f : X₁ ⟶ B} {ι
  : Y ⟶ B}
    (sq : IsPullback π g f ι) (κ : B' ⟶ B) (ι' : Y ⟶ B') (hι : ι' ≫ κ = ι) :
    ∃ π' : X ⟶ pullback f κ, IsPullback π' g (pullback.snd f κ) ι' := by
  have w : π ≫ f = (g ≫ ι') ≫ κ := by rw [Category.assoc, hι]; exact sq.w
  refine ⟨pullback.lift π (g ≫ ι') w, ?_⟩
  refine IsPullback.of_right (h₁₂ := pullback.fst f κ) (v₁₃ := f) (h₂₂ := κ) ?_ (pullback.lift_snd
    _ _ _)
    (IsPullback.of_hasPullback f κ)
  rw [pullback.lift_fst, hι]
  exact sq

lemma specMap_algebraMap_comp {T : Type u} [CommRing T] {A : Type u} [CommRing A] [Algebra T A]
    (T' : Subalgebra T A) :
    Spec.map (CommRingCat.ofHom (algebraMap ↥T' A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap T
      ↥T')) =
      Spec.map (CommRingCat.ofHom (algebraMap T A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

lemma package {A₀ B A : Type u} [CommRing A₀] [CommRing B] [CommRing A] [Algebra A₀ B] [Algebra B
  A] [Algebra A₀ A]
    [IsScalarTower A₀ B A] [Algebra.FiniteType A₀ B]
    (T₄ : Subalgebra B A) (hT₄ : T₄.FG) (s : Finset A) (hs : (↑s : Set A) ⊆ (T₄.restrictScalars A₀
      : Set A))
    {X X₀ : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T₄)) (π
      : X ⟶ X₀)
    (h1 : IsProper f₀) (h2 : Flat f₀)
    (h3 : IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₄ A)))) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Flat f₀ ∧ IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))
          := by
  have : Algebra.FiniteType B ↥T₄ := (Subalgebra.fg_iff_finiteType _).mp hT₄
  have hFT : Algebra.FiniteType A₀ ↥T₄ := Algebra.FiniteType.trans (S := B) inferInstance
    inferInstance
  exact ⟨T₄.restrictScalars A₀, (Subalgebra.fg_iff_finiteType _).mpr hFT, hs, X₀, f₀, π, h1, h2, h3⟩

end ApproxAux

open ApproxAux in
theorem _root_.AlgebraicGeometry.ProperFlatFinitePresentationDescent
    {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of A)) [IsProper g] [Flat g]
      [LocallyOfFinitePresentation g]
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of ↥T)) (π : X ⟶ X₀),
        IsProper f₀ ∧ Flat f₀ ∧ IsPullback π g f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥T A)))
          := by
  classical
  obtain ⟨T₁, hT₁, hsT₁, X₁, f₁, π₁, hlfp₁, hqc₁, hqs₁, sq₁⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation (A₀ := A₀) g s
  have := hlfp₁; have := hqc₁; have := hqs₁
  have : Algebra.FiniteType A₀ ↥T₁ := (Subalgebra.fg_iff_finiteType _).mp hT₁
  have : IsSeparated (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ A)))) :=
    (iff_of_isPullback (P := @IsSeparated) sq₁).mpr inferInstance
  obtain ⟨T₂, hT₂, -, hsep₂⟩ :=
    AlgebraicGeometry.IsSeparated.exists_fg_subalgebra_of_isSeparated_pullback_snd (A := A) f₁ ∅
  have := hsep₂
  have : Algebra.FiniteType ↥T₁ ↥T₂ := (Subalgebra.fg_iff_finiteType _).mp hT₂
  have : Algebra.FiniteType A₀ ↥T₂ := Algebra.FiniteType.trans (S := ↥T₁) inferInstance
    inferInstance
  have : IsNoetherianRing ↥T₂ := Algebra.FiniteType.isNoetherianRing A₀ ↥T₂
  let κ₂ : Spec (CommRingCat.of ↥T₂) ⟶ Spec (CommRingCat.of ↥T₁) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂))
  let f₂ : pullback f₁ κ₂ ⟶ Spec (CommRingCat.of ↥T₂) := pullback.snd f₁ κ₂
  obtain ⟨π₂, sq₂⟩ := exists_isPullback_of_fac sq₁ κ₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂
    A)))
    (specMap_algebraMap_comp T₂)
  have : LocallyOfFinitePresentation f₂ := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
      AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ₂) hlfp₁
  have : QuasiCompact f₂ := by
    have : MorphismProperty.IsStableUnderBaseChange
        (@QuasiCompact : MorphismProperty Scheme.{u}) :=
      AlgebraicGeometry.quasiCompact_isStableUnderBaseChange
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f₁ κ₂) hqc₁
  have : MorphismProperty.IsStableUnderBaseChange
      (@Flat : MorphismProperty Scheme.{u}) := AlgebraicGeometry.Flat.isStableUnderBaseChange
  have : Flat (pullback.snd f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A)))) := by
    have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
        (P := (@Flat : MorphismProperty Scheme.{u}))
    exact (iff_of_isPullback (P := (@Flat : MorphismProperty Scheme.{u})) sq₂).mpr
      inferInstance
  obtain ⟨T₃, hT₃, -, hflat₃⟩ :=
    AlgebraicGeometry.Flat.exists_fg_subalgebra_of_flat_pullback_snd (A := A) f₂ ∅
  obtain ⟨t₃, ht₃⟩ := hT₃
  have : IsProper (pullback.snd f₂ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ A)))) :=
    (iff_of_isPullback (P := @IsProper) sq₂).mpr inferInstance
  obtain ⟨T₄, hT₄, hs₄, hprop₄⟩ :=
    AlgebraicGeometry.IsProper.exists_fg_subalgebra_of_isProper_pullback_snd (A := A) f₂ t₃
  have h₃₄ : T₃ ≤ T₄ := by rw [← ht₃]; exact Algebra.adjoin_le hs₄
  let κ₄ : Spec (CommRingCat.of ↥T₄) ⟶ Spec (CommRingCat.of ↥T₂) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ ↥T₄ : ↥T₂ →+* ↥T₄))
  let f₄ := pullback.snd f₂ κ₄
  have := hprop₄
  have : Flat f₄ := by
    have := hflat₃
    let κ₃ : Spec (CommRingCat.of ↥T₃) ⟶ Spec (CommRingCat.of ↥T₂) :=
      Spec.map (CommRingCat.ofHom (algebraMap ↥T₂ ↥T₃ : ↥T₂ →+* ↥T₃))
    let κ₃₄ : Spec (CommRingCat.of ↥T₄) ⟶ Spec (CommRingCat.of ↥T₃) :=
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h₃₄).toRingHom)
    have hκ : κ₃₄ ≫ κ₃ = κ₄ := by
      simp only [κ₃₄, κ₃, κ₄, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
    obtain ⟨ρ, sqρ⟩ := exists_isPullback_of_fac (IsPullback.of_hasPullback f₂ κ₄) κ₃ κ₃₄ hκ
    exact MorphismProperty.of_isPullback
      (P := (@Flat : MorphismProperty Scheme.{u})) sqρ inferInstance
  obtain ⟨π₄, sq₄⟩ := exists_isPullback_of_fac sq₂ κ₄ (Spec.map (CommRingCat.ofHom (algebraMap ↥T₄
    A)))
    (specMap_algebraMap_comp T₄)
  have hflat₄ : Flat f₄ := inferInstance
  refine package T₄ hT₄ s ?_ g f₄ π₄ hprop₄ hflat₄ sq₄
  intro a ha
  have h1 : a ∈ T₁ := hsT₁ ha
  have h2 : a ∈ T₂ := T₂.algebraMap_mem (⟨a, h1⟩ : ↥T₁)
  have h4 : a ∈ T₄ := T₄.algebraMap_mem (⟨a, h2⟩ : ↥T₂)
  exact h4
end AlgebraicCurves.Geometry.Schemes.Proofs.ProperFlatFinitePresentationDescent
end ProofImplementation
