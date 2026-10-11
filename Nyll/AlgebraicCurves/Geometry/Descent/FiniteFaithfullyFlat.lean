/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_DescentAction_effective_of_finiteEtale.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

Local generalization to finitely presented faithfully flat finite algebras:
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Authors of the generalization: Naganori Yamaguchi (assisted by OpenAI Codex).
-/

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_isPullback_of_flat_surjective

/-!
# Effective descent along finite faithfully flat covers

The quotient of the actual finite locally free equivalence relation associated with a
covering action supplies its descended scheme. Finite presentation is sufficient;
no separability of the covering algebra is needed. In particular this applies to
arbitrary finite field extensions, including purely inseparable ones.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DescentAction

/-- A descent action over a finite, finitely presented, faithfully flat algebra is effective
when every finite set of points of its source has an affine neighborhood. -/
theorem effective_of_finite_faithfullyFlat
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [Algebra.FinitePresentation R R'] [Module.FaithfullyFlat R R']
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
      rw [Set.Finite.mem_toFinset]; exact ⟨r, hr, rfl⟩)⟩
  obtain ⟨Y, p, w, _, hpflat, _, hpsurj, hR, ⟨hcolim⟩⟩ :=
    AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst (x' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))) A.act
      (fun a b h₁ h₂ => A.hom_ext h₁ h₂) (fun T => A.equivalence T) haff'
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

/-- Effective descent along any finite field extension. Finite presentation follows from
finite generation over the Noetherian base field, and faithful flatness from the nonzero
vector-space structure of the extension. -/
theorem effective_of_finite_fieldExtension
    (K L : Type u) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    {X' : Scheme.{u}} {x' : X' ⟶ Spec (CommRingCat.of L)}
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap K L))) x')
    (haff : ∀ S : Finset X', ∃ U : X'.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    A.Effective := by
  have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact effective_of_finite_faithfullyFlat K L A haff

end AlgebraicGeometry.DescentAction
