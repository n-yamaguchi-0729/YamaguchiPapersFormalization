/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgHom_exists_cotangent_linearMap_of_fst_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Alg Hom exists cotangent linear Map of fst eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.AlgHom_exists_cotangent_linearMap_of_fst_eq

universe u v x

theorem _root_.AlgHom.exists_cotangent_linearMap_of_fst_eq
    {𝒪 : Type u} [CommRing 𝒪] {R : Type v} [CommRing R] [Algebra 𝒪 R] (πR : R →ₐ[𝒪] 𝒪)
    {N : Type x} [AddCommGroup N] [Module 𝒪 N] [Module 𝒪ᵐᵒᵖ N] [IsCentralScalar 𝒪 N]
    (ψ : R →ₐ[𝒪] TrivSqZeroExt 𝒪 N) (hψ : ∀ r : R, (ψ r).fst = πR r) :
    ∃ f : (RingHom.ker πR).Cotangent →ₗ[𝒪] N,
      ∀ a : RingHom.ker πR, (ψ (a : R)).snd = f ((RingHom.ker πR).toCotangent a) := by
  let g : RingHom.ker πR →ₗ[𝒪] N :=
    { toFun := fun a => (ψ (a : R)).snd
      map_add' := fun a b => by
        simp only [Submodule.coe_add, map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        simp only [Submodule.coe_smul_of_tower, map_smul, TrivSqZeroExt.snd_smul, RingHom.id_apply]
          }
  have hg : ∀ x y : RingHom.ker πR, g (x * y) = 0 := fun x y => by
    change (ψ ((x * y : RingHom.ker πR) : R)).snd = 0
    have hxy : ((x * y : RingHom.ker πR) : R) = (x : R) * (y : R) := rfl
    rw [hxy, map_mul, TrivSqZeroExt.snd_mul, hψ, hψ, RingHom.mem_ker.mp x.2, RingHom.mem_ker.mp y.2,
      MulOpposite.op_zero, zero_smul, zero_smul, add_zero]
  exact ⟨Ideal.Cotangent.lift g hg, fun a => (Ideal.Cotangent.lift_toCotangent g hg a).symm⟩
end AlgebraicCurves.Foundations.Algebra.Proofs.AlgHom_exists_cotangent_linearMap_of_fst_eq
end ProofImplementation
