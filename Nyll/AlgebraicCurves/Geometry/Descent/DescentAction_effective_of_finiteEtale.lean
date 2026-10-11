/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Etale.Basic
import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_isPullback_of_flat_surjective

/-!
# Descent Action effective of finite Etale
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Descent.Proofs.DescentAction_effective_of_finiteEtale

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem _root_.AlgebraicGeometry.DescentAction.effective_of_finiteEtale
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of R')}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by
  classical
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      change RingHom.Flat (algebraMap R R'); exact RingHom.flat_algebraMap_iff.2 inferInstance)
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (IsFinite.SpecMap_iff _).2
      (by change (algebraMap R R').Finite; exact RingHom.finite_algebraMap.mpr inferInstance)
  have hlofp : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (by
      change (algebraMap R R').FinitePresentation
      exact RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have := hflat; have := hfin; have := hlofp
  have hAffine : HasAffineProperty (@IsFinite : MorphismProperty Scheme.{u})
      (affineAnd RingHom.Finite) :=
    (HasAffineProperty.affineAnd_iff (@IsFinite : MorphismProperty Scheme.{u})
      RingHom.finite_respectsIso RingHom.finite_localizationPreserves.away
      RingHom.finite_ofLocalizationSpan).mpr (fun {_ _} f => isFinite_iff f)
  have hbcFin : MorphismProperty.IsStableUnderBaseChange
      (@IsFinite : MorphismProperty Scheme.{u}) :=
    HasAffineProperty.affineAnd_isStableUnderBaseChange hAffine
      RingHom.finite_respectsIso RingHom.finite_isStableUnderBaseChange
  have hbcFlat : MorphismProperty.IsStableUnderBaseChange
      (@Flat : MorphismProperty Scheme.{u}) := Flat.isStableUnderBaseChange
  have hbcLfp : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    locallyOfFinitePresentation_isStableUnderBaseChange
  have : IsFinite (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := hbcFin.of_isPullback
      (IsPullback.of_hasPullback
        (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).flip hfin
  have : Flat (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := hbcFlat.of_isPullback
      (IsPullback.of_hasPullback
        (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).flip hflat
  have : LocallyOfFinitePresentation (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R
    R')))
    (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := hbcLfp.of_isPullback
      (IsPullback.of_hasPullback
        (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).flip hlofp
  have : IsFinite A.act := by rw [A.act_eq_invol_fst]; infer_instance
  have : Flat A.act := by rw [A.act_eq_invol_fst]; infer_instance
  have : LocallyOfFinitePresentation A.act := by rw [A.act_eq_invol_fst]; infer_instance
  have haff' : ∀ x : X', ∃ U : X'.Opens, IsAffineOpen U ∧
      ∀ r : ↑(pullback (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))) r = x → A.act r ∈ U := by
    intro x
    have hfinite := (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))).finite_preimage_singleton x
    obtain ⟨U, hU, hSU⟩ := haff ((hfinite.image fun r => A.act r).toFinset)
    exact ⟨U, hU, fun r hr => hSU _ (by
      rw [Set.Finite.mem_toFinset]; exact ⟨r, by simpa using hr, rfl⟩)⟩
  obtain ⟨Y, p, w, _, hpflat, _, hpsurj, hR, ⟨hcolim⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))) A.act
      (fun a b h₁ h₂ => A.hom_ext h₁ h₂) (fun T => A.equivalence T) haff'
  have := hpflat; have := hpsurj
  have : QuasiCompact p := inferInstance
  have hco : pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫ x' ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R R')) =
      A.act ≫ x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := by
    rw [pullback.condition, reassoc_of% A.act_comp]
  obtain ⟨f, hpf⟩ := Cofork.IsColimit.desc' hcolim (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R
    R'))) hco
  obtain ⟨e, he, -, hc⟩ :=
    AlgebraicGeometry.DescentAction.effective_of_isPullback_of_flat_surjective
    (Spec.map (CommRingCat.ofHom (algebraMap R R'))) A p w hR f hpf
  exact ⟨Y, f, e, he, hc⟩
end AlgebraicCurves.Geometry.Descent.Proofs.DescentAction_effective_of_finiteEtale
end ProofImplementation
