/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow

/-!
# Mv Polynomial finrank piece sup span singleton succ add finrank piece eq of forall mul mem
imp
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayHyperplaneRank

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace P2mWs6HP

variable {K : Type} [Field K] {n : ℕ}

/-- The degree-d homogeneous polynomials belonging to the ideal J. -/
abbrev Jd (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ) : Submodule K
  ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) :=
  Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d).subtype (J.restrictScalars
    K)

theorem mem_Jd (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ) (p :
  ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d)) : p ∈ Jd J d ↔ (p : MvPolynomial (Fin (n
  + 1)) K) ∈ J := by
  simp [Jd, Submodule.mem_comap, Submodule.restrictScalars_mem]

scoped instance finite_homogeneousSubmodule (d : ℕ) : Module.Finite K
  ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) := by
  have hle : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d ≤ MvPolynomial.restrictTotalDegree
    (Fin (n + 1)) K d := by
    intro p hp
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact ((MvPolynomial.mem_homogeneousSubmodule d p).mp hp).totalDegree_le
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

/-- Multiplication by the homogeneous linear polynomial, raising degree by one. -/
noncomputable def mulLin (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1) (d : ℕ) :
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) →ₗ[K]
      ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K (d + 1)) where
  toFun p := ⟨(p : MvPolynomial (Fin (n + 1)) K) * ℓ, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact ((MvPolynomial.mem_homogeneousSubmodule d p.1).mp p.2).mul hℓ⟩
  map_add' p q := by ext; simp [add_mul]
  map_smul' c p := by ext; simp [MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem mulLin_apply (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1) (d : ℕ) (p :
  ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d)) :
    (mulLin ℓ hℓ d p : MvPolynomial (Fin (n + 1)) K) = (p : MvPolynomial (Fin (n + 1)) K) * ℓ := rfl

theorem homogeneousComponent_mul_linear (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (h : MvPolynomial (Fin (n + 1)) K) (d : ℕ) :
    MvPolynomial.homogeneousComponent (d + 1) (h * ℓ) = MvPolynomial.homogeneousComponent d h * ℓ
      := by
  have := DirectSum.coe_decompose_mul_add_of_right_mem (MvPolynomial.homogeneousSubmodule (Fin (n +
    1)) K)
    (a := h) (i := d) ((MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ)
  rw [← MvPolynomial.decomposition.decompose'_apply, ← MvPolynomial.decomposition.decompose'_apply]
  rw [DirectSum.Decomposition.decompose'_eq]
  exact this

end P2mWs6HP

attribute [local instance] P2mWs6HP.finite_homogeneousSubmodule
end
end AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayHyperplaneRank

namespace MvPolynomial
noncomputable section

open _root_.AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayHyperplaneRank
open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
  _root_.AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] P2mWs6HP.finite_homogeneousSubmodule



open P2mWs6HP in
theorem finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp
    (n : ℕ) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    (hcolon : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) K), F.IsHomogeneous d → ℓ * F ∈ J → F ∈ J)
    (d : ℕ) :
    Module.finrank K (piece (J ⊔ Ideal.span {ℓ}) (d + 1)) + Module.finrank K (piece J d) =
      Module.finrank K (piece J (d + 1)) := by
  classical
  let φ : ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) →ₗ[K] piece J (d + 1) := (Jd J (d
    + 1)).mkQ ∘ₗ mulLin ℓ hℓ d
  have hker : LinearMap.ker φ = Jd J d := by
    ext p
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, mem_Jd, mem_Jd,
      mulLin_apply]
    constructor
    · intro h
      exact hcolon d p.1 ((MvPolynomial.mem_homogeneousSubmodule d p.1).mp p.2)
        (by rwa [mul_comm] at h)
    · intro h
      exact Ideal.mul_mem_right _ _ h
  have hrange : LinearMap.range φ = (Jd J (d + 1) ⊔ LinearMap.range (mulLin ℓ hℓ d)).map (Jd J (d +
    1)).mkQ := by
    rw [LinearMap.range_comp, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  have hJl : Jd (J ⊔ Ideal.span {ℓ}) (d + 1) = Jd J (d + 1) ⊔ LinearMap.range (mulLin ℓ hℓ d) := by
    apply le_antisymm
    · intro G hG
      rw [mem_Jd] at hG
      obtain ⟨j, hj, s, hs, hGjs⟩ := Submodule.mem_sup.mp hG
      obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hs
      have hGhom : (G : MvPolynomial (Fin (n + 1)) K).IsHomogeneous (d + 1) :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp G.2
      have hGeq : MvPolynomial.homogeneousComponent (d + 1) (G : MvPolynomial (Fin (n + 1)) K) = G
        := by
        rw [MvPolynomial.homogeneousComponent_of_mem G.2, ite_eq_left rfl]
      have hdec : (G : MvPolynomial (Fin (n + 1)) K) =
          MvPolynomial.homogeneousComponent (d + 1) j + MvPolynomial.homogeneousComponent d h * ℓ
            := by
        rw [← hGeq, ← hGjs, map_add, homogeneousComponent_mul_linear ℓ hℓ h d]
      rw [Submodule.mem_sup]
      refine ⟨⟨MvPolynomial.homogeneousComponent (d + 1) j, MvPolynomial.homogeneousComponent_mem _
        _⟩, ?_,
        mulLin ℓ hℓ d ⟨MvPolynomial.homogeneousComponent d h, MvPolynomial.homogeneousComponent_mem
          _ _⟩,
        LinearMap.mem_range_self _ _, ?_⟩
      · rw [mem_Jd]; exact hJ j hj (d + 1)
      · apply Subtype.ext
        rw [Submodule.coe_add, mulLin_apply, hdec]
    · refine sup_le ?_ ?_
      · intro p hp
        rw [mem_Jd] at hp ⊢
        exact Submodule.mem_sup_left hp
      · rintro _ ⟨p, rfl⟩
        rw [mem_Jd, mulLin_apply]
        exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨p, rfl⟩)
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 := (Jd J d).finrank_quotient_add_finrank
  have h3 := (LinearMap.range φ).finrank_quotient_add_finrank
  have h4 : Module.finrank K (piece J (d + 1) ⧸ LinearMap.range φ) = Module.finrank K (piece (J ⊔
    Ideal.span {ℓ}) (d + 1)) := by
    rw [hrange]
    exact ((Submodule.quotientQuotientEquivQuotient (Jd J (d + 1)) (Jd J (d + 1) ⊔ LinearMap.range
      (mulLin ℓ hℓ d))
      le_sup_left).trans (Submodule.quotEquivOfEq _ _ hJl.symm)).finrank_eq
  rw [hker] at h1
  have h2' : Module.finrank K (piece J d) + Module.finrank K ↥(Jd J d) = Module.finrank K
    ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d) := h2
  have h3' : Module.finrank K (piece J (d + 1) ⧸ LinearMap.range φ) + Module.finrank K
    ↥(LinearMap.range φ) =
      Module.finrank K (piece J (d + 1)) := h3
  omega

end

open _root_.AlgebraicCurves.Foundations.Polynomial.Proofs.MacaulayHyperplaneRank
attribute [local instance] P2mWs6HP.finite_homogeneousSubmodule

end MvPolynomial
end ProofImplementation
