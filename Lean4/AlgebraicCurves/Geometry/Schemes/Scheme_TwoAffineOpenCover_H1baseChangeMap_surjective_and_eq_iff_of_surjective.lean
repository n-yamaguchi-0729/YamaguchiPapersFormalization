/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Tactic.Abel
import AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf

/-!
# Scheme Two Affine Open Cover H1base Change Map surjective and eq iff of surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

open scoped TensorProduct

namespace PicTanH1BC

section Algebra

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

theorem exists_eq_one_tmul (hA : Function.Surjective (algebraMap R A)) {P : Type*} [AddCommGroup P]
  [Module R P]
    (w : A ⊗[R] P) : ∃ p : P, w = (1 : A) ⊗ₜ[R] p := by
  induction w using TensorProduct.inductionOn with
  | tmul a p =>
    obtain ⟨r, rfl⟩ := hA a
    exact ⟨r • p, by rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
  | add w w' hw hw' =>
    obtain ⟨p, rfl⟩ := hw
    obtain ⟨p', rfl⟩ := hw'
    exact ⟨p + p', (TensorProduct.tmul_add _ _ _).symm⟩

theorem one_tmul_eq_one_tmul_iff (hA : Function.Surjective (algebraMap R A)) {M : Type*}
  [AddCommGroup M]
    [Module R M] (m n : M) :
    (1 : A) ⊗ₜ[R] m = (1 : A) ⊗ₜ[R] n ↔ m - n ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R M)
      := by
  have hA' : Function.Surjective (Algebra.ofId R A) := fun a => hA a
  have hk : RingHom.ker (Algebra.ofId R A) = RingHom.ker (algebraMap R A) := Ideal.ext fun _ =>
    Iff.rfl
  let e : (R ⧸ RingHom.ker (Algebra.ofId R A)) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hA'
  let Ψ : A ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker (Algebra.ofId R A) • (⊤ : Submodule R M)) :=
    TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (Algebra.ofId R A))
  have hΨ : ∀ x : M, Ψ ((1 : A) ⊗ₜ[R] x) = Submodule.Quotient.mk x := fun x => by
    simp only [Ψ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      map_one,
      LinearEquiv.refl_apply]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x
  rw [← hk, ← Ψ.injective.eq_iff, hΨ, hΨ, Submodule.Quotient.eq]

theorem smul_top_quotient {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R
  M) :
    (I • (⊤ : Submodule R (M ⧸ N))) = (I • (⊤ : Submodule R M)).map N.mkQ := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

theorem one_tmul_mem_range_baseChange_iff (hA : Function.Surjective (algebraMap R A))
    {P M : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] (d : P →ₗ[R] M) (p :
      M) :
    (1 : A) ⊗ₜ[R] p ∈ LinearMap.range (d.baseChange A) ↔
      (Submodule.Quotient.mk p : M ⧸ LinearMap.range d) ∈
        RingHom.ker (algebraMap R A) • (⊤ : Submodule R (M ⧸ LinearMap.range d)) := by
  rw [smul_top_quotient, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨s, rfl⟩ := exists_eq_one_tmul hA v
    rw [LinearMap.baseChange_tmul] at hv
    refine ⟨p - d s, (one_tmul_eq_one_tmul_iff hA p (d s)).1 hv.symm, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2
      (LinearMap.mem_range_self d s),
      sub_zero]
  · rintro ⟨p', hp', hpp'⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hpp'
    obtain ⟨s, hs⟩ := LinearMap.mem_range.1 hpp'
    have h1 : (1 : A) ⊗ₜ[R] p' = (1 : A) ⊗ₜ[R] (0 : M) :=
      (one_tmul_eq_one_tmul_iff hA p' 0).2 (by rw [sub_zero]; exact hp')
    have hp : p = p' - d s := by rw [hs]; abel
    refine ⟨(1 : A) ⊗ₜ[R] (-s), ?_⟩
    rw [LinearMap.baseChange_tmul, map_neg, hp, TensorProduct.tmul_sub, h1,
      TensorProduct.tmul_zero, zero_sub,
      TensorProduct.tmul_neg]

end Algebra

section Main

theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec
  (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) :=
          by
  obtain ⟨e0, e1, e01, eH0, eH1, h0, h1, h01, hH0, hH1⟩ :=
    Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c A
  have hβ : ∀ m : (𝒱.cover c).A01, 𝒱.H1baseChangeMap c A (Submodule.Quotient.mk m) =
      eH1 (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] m)) := by
    intro m
    rw [hH1, h01, H1baseChangeMap_mk, baseChange_map01_apply]
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨q, rfl⟩ := eH1.surjective z
    induction q using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨m, rfl⟩ := exists_eq_one_tmul hA w
      exact ⟨Submodule.Quotient.mk m, hβ m⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      induction y using Submodule.Quotient.induction_on with
      | H n =>
        rw [hβ, hβ, eH1.injective.eq_iff, Submodule.Quotient.eq, ← TensorProduct.tmul_sub,
          ← Submodule.Quotient.mk_sub]
        exact one_tmul_mem_range_baseChange_iff hA _ (m - n)

end Main

end PicTanH1BC

end Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective
end AlgebraicCurves.Geometry.Schemes.Proofs

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

universe u

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs in
open Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective in
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra in
open scoped TensorProduct in
open AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem H1baseChangeMap_surjective_and_eq_iff_of_surjective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) :=
  PicTanH1BC.main 𝒱 c A hA
end AlgebraicGeometry.Scheme.TwoAffineOpenCover
end ProofImplementation
