/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Cohomology.Sheaves.OrderedAffineCoverCochainPullback
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction

/-!
# Small Extension is Fibre Reading zero add mul neg restrict and exists is Fibre Reading
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Deformation.Proofs.FibreReadingExistence

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


universe u

end AlgebraicCurves.Geometry.Deformation.Proofs.FibreReadingExistence

section
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.IsLocalRing
open _root_.AlgebraicGeometry.SmallExtension
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicCurves.Geometry.Deformation.Proofs.FibreReadingExistence
namespace AlgebraicGeometry

theorem SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X)
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) :
    IsFibreReading V ι f fk i U W hW 0 0 ∧
    (∀ (δ δ' : Γ(X, U)) (w w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w → IsFibreReading V ι f fk i U W hW δ' w' →
          IsFibreReading V ι f fk i U W hW (δ + δ') (w + w')) ∧
    (∀ (δ s : Γ(X, U)) (w w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w →
          (∀ ξ : Module.Dual k V, w' ξ =
            (show Γ(Xk, W) from (OModulePresheaf.unit fk).res hW
              (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app U).hom s)) • w ξ) →
          IsFibreReading V ι f fk i U W hW (s * δ) w') ∧
    (∀ (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W),
        IsFibreReading V ι f fk i U W hW δ w → IsFibreReading V ι f fk i U W hW (-δ) (-w)) ∧
    (∀ (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
        (U' : X.Opens) (W' : Xk.Opens) (hU' : U' ≤ U) (hW'W : W' ≤ W) (hW' : W' ≤ i ⁻¹ᵁ U'),
        IsFibreReading V ι f fk i U W hW δ w →
          IsFibreReading V ι f fk i U' W' hW' ((X.presheaf.map (homOfLE hU').op).hom δ)
            (((OModulePresheaf.unit fk).res hW'W).comp w)) ∧
    (∀ δ : Γ(X, U), (letI := algebraOfHom f U
        δ ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι)) →
        ∃ w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W, IsFibreReading V ι f fk i U W
          hW δ w) := by
  classical
  let instU : Algebra B₁ Γ(X, U) := Scheme.TwoAffineOpenCover.algebraOfHom f U
  let instW : Algebra k Γ(Xk, W) := Scheme.TwoAffineOpenCover.algebraOfHom fk W
  let ρ : Γ(X, U) → (OModulePresheaf.unit fk).obj W := fun x =>
    (OModulePresheaf.unit fk).res hW (show (OModulePresheaf.unit fk).obj (i ⁻¹ᵁ U) from (i.app
      U).hom x)
  have hρ : ∀ x, ρ x = (show (OModulePresheaf.unit fk).obj W from
      (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom x)) := fun x => rfl
  have hρ_mul : ∀ x y, ρ (x * y) = (show Γ(Xk, W) from ρ x) * (show Γ(Xk, W) from ρ y) := by
    intro x y
    change (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom (x * y)) =
      (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom x) * (Xk.presheaf.map (homOfLE
        hW).op).hom ((i.app U).hom y)
    rw [map_mul, map_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, Fin.elim0, Fin.elim0, by simp, fun ξ => by simp⟩
  · rintro δ δ' w w' ⟨n₁, v₁, s₁, h₁, hw₁⟩ ⟨n₂, v₂, s₂, h₂, hw₂⟩
    refine ⟨n₁ + n₂, Fin.append v₁ v₂, Fin.append s₁ s₂, ?_, ?_⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [h₁, h₂]
    · intro ξ
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← hw₁ ξ, ← hw₂ ξ]
      rfl
  · rintro δ s w w' ⟨n, v, t, h₁, hw₁⟩ hw'
    refine ⟨n, v, fun j => s * t j, ?_, ?_⟩
    · rw [← h₁, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro ξ
      rw [hw' ξ, hw₁ ξ, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      change (show Γ(Xk, W) from ρ s) * ((algebraMap k Γ(Xk, W) (ξ (v j))) * (show Γ(Xk, W) from ρ
        (t j))) =
        (algebraMap k Γ(Xk, W) (ξ (v j))) * (show Γ(Xk, W) from ρ (s * t j))
      rw [hρ_mul]
      ring
  · rintro δ w ⟨n, v, s, h₁, hw₁⟩
    refine ⟨n, v, fun j => - s j, ?_, ?_⟩
    · rw [← h₁, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro ξ
      have hneg : (-w) ξ = -(w ξ) := rfl
      rw [hneg, hw₁ ξ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only
      rw [map_neg, ← smul_neg]
      congr 1
      exact (LinearMap.map_neg _ _).symm
  · rintro δ w U' W' hU' hW'W hW' ⟨n, v, s, h₁, hw₁⟩
    let instU' : Algebra B₁ Γ(X, U') := Scheme.TwoAffineOpenCover.algebraOfHom f U'
    refine ⟨n, v, fun j => (X.presheaf.map (homOfLE hU').op).hom (s j), ?_, ?_⟩
    · rw [← h₁, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      congr 1
      exact ((Scheme.TwoAffineOpenCover.restrictAlgHom f hU').commutes (ι (v j))).symm
    · intro ξ
      rw [LinearMap.comp_apply, hw₁ ξ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.map_smul]
      congr 1
      change ((i.app U ≫ Xk.presheaf.map (homOfLE hW).op) ≫ Xk.presheaf.map (homOfLE hW'W).op).hom
        (s j) =
        ((X.presheaf.map (homOfLE hU').op ≫ i.app U') ≫ Xk.presheaf.map (homOfLE hW').op).hom (s j)
      rw [Scheme.Hom.naturality]
      simp only [Category.assoc, ← Functor.map_comp]
      rfl
  · intro δ hδ
    rw [Ideal.map] at hδ
    obtain ⟨n, c, g, hsum⟩ := (Submodule.mem_span_set').1 hδ
    have hg : ∀ j, ∃ vj : V, algebraMap B₁ Γ(X, U) (ι vj) = (g j : Γ(X, U)) := by
      intro j
      obtain ⟨y, ⟨vj, rfl⟩, hy⟩ := (g j).2
      exact ⟨vj, hy⟩
    choose v hv using hg
    refine ⟨∑ j, (Module.Dual.eval k V (v j)).smulRight (ρ (c j)), n, v, c, ?_, ?_⟩
    · rw [← hsum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hv j, smul_eq_mul, mul_comm]
    · intro ξ
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Module.Dual.eval_apply]
      rfl
end AlgebraicGeometry
end
end ProofImplementation
