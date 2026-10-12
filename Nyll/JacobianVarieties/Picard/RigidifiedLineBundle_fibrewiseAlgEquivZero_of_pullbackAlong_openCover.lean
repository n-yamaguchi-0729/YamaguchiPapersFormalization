/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Mathlib.Util.WithWeakNamespace

/-!
Descend fibrewise algebraic triviality of rigidified line bundles from an open cover of the
base.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
    NeronModelInfra

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem fibrewiseAlgEquivZero_of_pullbackAlong_openCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M : RigidifiedLineBundle c ε t) (h : ∀ i, FibrewiseAlgEquivZero (M.pullbackAlong (f i))) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ σ
  obtain ⟨i, hi⟩ := hf (σ.base (IsLocalRing.closedPoint k))
  have hrange : Set.range σ.base ⊆ Set.range (f i).1.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    exact hi
  let σ' : Spec (CommRingCat.of k) ⟶ U i := IsOpenImmersion.lift (f i).1 σ hrange
  have hσ' : σ' ≫ (f i).1 = σ := IsOpenImmersion.lift_fac _ _ _
  set ψ : SchemeHomOver (u i) t := f i with hψ
  have w : (pullback.fst (pullback.snd c t) σ ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) σ ≫ σ') ≫ u i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc,
      ← ψ.2, reassoc_of% hσ']
  let a : pullback (pullback.snd c t) σ ⟶ pullback c (u i) := pullback.lift _ _ w
  let e' : pullback (pullback.snd c t) σ ⟶ pullback (pullback.snd c (u i)) σ' :=
    pullback.lift a (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have he' : e' ≫ fibreAt c (u i) σ' = fibreAt c t σ := by
    simp only [e', fibreAt, pullback.lift_snd]
  have ha : a ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    apply pullback.hom_ext
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hσ']
      exact pullback.condition.symm
  have hcomp : (e' ≫ pullback.fst (pullback.snd c (u i)) σ') ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) σ := by
    rw [show e' ≫ pullback.fst _ _ = a from pullback.lift_fst _ _ _, ha]
  refine IsAlgEquivZero.of_iso ?_ ((h i k σ').pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L
end RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover
end JacobianVarieties.Picard.Proofs
end ProofImplementation
