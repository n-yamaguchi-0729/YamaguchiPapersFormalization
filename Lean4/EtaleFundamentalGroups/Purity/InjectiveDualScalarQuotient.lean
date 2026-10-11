/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Scalar quotients of injective-valued duals

If the image of a map is the kernel of a scalar endomorphism, the dual
map embeds the scalar quotient of the dual into the dual of the source.
A functional vanishing on the kernel factors through the scalar image;
injectivity of the values extends it from that image to the whole module.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u

open scoped Pointwise

variable {R A B E : Type u} [CommRing R]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]
variable [AddCommGroup E] [Module R E] [Module.Injective R E]

/-- Dualizing an exact pair whose second map is scalar multiplication
embeds the scalar quotient of the middle dual into the first dual. -/
theorem exists_injective_dual_scalarQuotient_of_exact
    (δ : A →ₗ[R] B) (x : R)
    (hex : Function.Exact δ (x • (LinearMap.id : B →ₗ[R] B))) :
    ∃ f : ((B →ₗ[R] E) ⧸ x • (⊤ : Submodule R (B →ₗ[R] E))) →ₗ[R]
        (A →ₗ[R] E), Function.Injective f := by
  let q : B →ₗ[R] B := x • LinearMap.id
  let pre : (B →ₗ[R] E) →ₗ[R] (A →ₗ[R] E) := LinearMap.lcomp R E δ
  let T : Submodule R (B →ₗ[R] E) := x • ⊤
  have hker : LinearMap.ker pre = T := by
    apply le_antisymm
    · intro φ hφ
      have hφzero : pre φ = 0 := hφ
      have hqφ : LinearMap.ker q ≤ LinearMap.ker φ := by
        intro b hb
        obtain ⟨a, ha⟩ := (hex b).mp hb
        rw [← ha]
        exact DFunLike.congr_fun hφzero a
      let g : LinearMap.range q →ₗ[R] E :=
        ((LinearMap.ker q).liftQ φ hqφ).comp q.quotKerEquivRange.symm.toLinearMap
      obtain ⟨ψ, hψ⟩ := Module.Injective.out
        (LinearMap.range q).subtype (LinearMap.range q).subtype_injective g
      have hψb (b : B) : ψ (q b) = φ b := by
        have h := hψ ⟨q b, LinearMap.mem_range_self q b⟩
        change ψ (q b) = (LinearMap.ker q).liftQ φ hqφ
          (q.quotKerEquivRange.symm ⟨q b, LinearMap.mem_range_self q b⟩) at h
        rw [LinearMap.quotKerEquivRange_symm_apply_image] at h
        exact h
      apply (Submodule.mem_smul_pointwise_iff_exists φ x ⊤).mpr
      refine ⟨ψ, Submodule.mem_top, ?_⟩
      ext b
      change x • ψ b = φ b
      rw [← map_smul]
      exact hψb b
    · intro φ hφ
      obtain ⟨ψ, _hψ, rfl⟩ :=
        (Submodule.mem_smul_pointwise_iff_exists φ x ⊤).mp hφ
      change pre (x • ψ) = 0
      ext a
      change x • ψ (δ a) = 0
      rw [← map_smul]
      have hxδ : x • δ a = 0 := hex.apply_apply_eq_zero a
      rw [hxδ, map_zero]
  refine ⟨T.liftQ pre hker.symm.le, ?_⟩
  exact LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot T pre hker.symm.le hker.le)

end EtaleFundamentalGroups.Purity

end
