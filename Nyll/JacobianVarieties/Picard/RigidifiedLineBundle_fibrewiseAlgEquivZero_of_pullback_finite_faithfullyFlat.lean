/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase

/-!
# Fibrewise algebraic equivalence under faithful flat base change

Lift geometric points through a finite faithfully flat morphism to descend algebraic equivalence.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FibrewiseDescent

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve NeronModelInfra

open scoped TensorProduct

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RigidifiedLineBundle
theorem fibrewiseAlgEquivZero_of_pullback_finite_faithfullyFlat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c ε t)
    (h : FibrewiseAlgEquivZero (M.pullbackAlong
        ⟨pullback.fst t (specMap R R'), pullback.condition⟩)) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Spec (CommRingCat.of k) ⟶ pullback t (specMap R R'),
      σ' ≫ pullback.fst t (specMap R R') = σ := by
    let ρ : CommRingCat.of R ⟶ CommRingCat.of k := (Spec.fullyFaithful.preimage (σ ≫ t)).unop
    have hρ : Spec.map ρ = σ ≫ t := Spec.fullyFaithful.map_preimage (σ ≫ t)
    let : Algebra R k := ρ.hom.toAlgebra
    have : Nontrivial (k ⊗[R] R') := inferInstance
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] R')
    let : Field ((k ⊗[R] R') ⧸ m) := Ideal.Quotient.field m
    have : Module.Finite k ((k ⊗[R] R') ⧸ m) := inferInstance
    have : Algebra.IsIntegral k ((k ⊗[R] R') ⧸ m) := Algebra.IsIntegral.of_finite k _
    have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := (k ⊗[R] R') ⧸ m)
    let ι : ((k ⊗[R] R') ⧸ m) ≃+* k :=
      (RingEquiv.ofBijective (algebraMap k ((k ⊗[R] R') ⧸ m)) hbij).symm
    let g : R' →+* k :=
      ι.toRingHom.comp
        ((Ideal.Quotient.mk m).comp
          (Algebra.TensorProduct.includeRight (R := R) (A := k)).toRingHom)
    have hg : g.comp (algebraMap R R') = ρ.hom := by
      ext r
      change ι (Ideal.Quotient.mk m (Algebra.TensorProduct.includeRight (R := R) (A := k)
          (algebraMap R R' r))) =
        algebraMap R k r
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R k (k ⊗[R] R'),
        ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
      exact (RingEquiv.ofBijective (algebraMap k ((k ⊗[R] R') ⧸ m)) hbij).symm_apply_apply _
    let τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R') := Spec.map (CommRingCat.ofHom g)
    have hτ : σ ≫ t = τ ≫ specMap R R' := by
      rw [← hρ]
      change Spec.map ρ = Spec.map (CommRingCat.ofHom g) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R'))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg, CommRingCat.ofHom_hom]
    exact ⟨pullback.lift σ τ hτ, pullback.lift_fst _ _ _⟩
  set ψ : SchemeHomOver (pullback.snd t (specMap R R') ≫ specMap R R') t :=
    ⟨pullback.fst t (specMap R R'), pullback.condition⟩ with hψ
  have w : (pullback.fst (pullback.snd c t) σ ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) σ ≫ σ') ≫
        (pullback.snd t (specMap R R') ≫ specMap R R') := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc,
      ← pullback.condition, reassoc_of% hσ']
  let a : pullback (pullback.snd c t) σ ⟶
      pullback c (pullback.snd t (specMap R R') ≫ specMap R R') :=
    pullback.lift _ _ w
  let e' : pullback (pullback.snd c t) σ
      ⟶ pullback (pullback.snd c (pullback.snd t (specMap R R') ≫ specMap R R')) σ' :=
    pullback.lift a (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have he' : e' ≫ fibreAt c (pullback.snd t (specMap R R') ≫ specMap R R') σ' = fibreAt c t σ := by
    simp only [e', fibreAt, pullback.lift_snd]
  have ha : a ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    apply pullback.hom_ext
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      change pullback.snd (pullback.snd c t) σ ≫ σ' ≫ pullback.fst t (specMap R R') = _
      rw [hσ']
      exact pullback.condition.symm
  have hcomp : (e' ≫
      pullback.fst (pullback.snd c (pullback.snd t (specMap R R') ≫ specMap R R')) σ') ≫
      baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    rw [show e' ≫ pullback.fst _ _ = a from pullback.lift_fst _ _ _, ha]
  refine IsAlgEquivZero.of_iso ?_ ((h k σ').pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L
end JacobianVarieties.Picard.Proofs.FibrewiseDescent
end ProofImplementation
