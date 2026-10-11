/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FormallySmooth_formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Etale.Basic

/-!
# Algebra Formally Smooth formally Smooth and formally Unramified aeval of exists Unique
smul D eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.FormallySmoothEvaluation

open Polynomial

universe u v

namespace EtaleCoordinate

variable {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S]

theorem exists_eq_tmul_D_X [Algebra A[X] S] [IsScalarTower A A[X] S]
    (z : TensorProduct A[X] S (Ω[A[X]⁄A])) :
    ∃ s : S, z = s ⊗ₜ[A[X]] KaehlerDifferential.D A A[X] X := by
  induction z using TensorProduct.inductionOn with
  | tmul s ω =>
    have hω : ω = (KaehlerDifferential.polynomialEquiv A ω) • KaehlerDifferential.D A A[X] X := by
      conv_lhs => rw [← (KaehlerDifferential.polynomialEquiv A).symm_apply_apply ω]
      exact KaehlerDifferential.polynomialEquiv_symm A _
    refine ⟨(KaehlerDifferential.polynomialEquiv A ω) • s, ?_⟩
    conv_lhs => rw [hω]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨s₁, rfl⟩ := hx
    obtain ⟨s₂, rfl⟩ := hy
    exact ⟨s₁ + s₂, by rw [TensorProduct.add_tmul]⟩

theorem mapBaseChange_tmul_D_X [Algebra A[X] S] [IsScalarTower A A[X] S] (s : S) :
    KaehlerDifferential.mapBaseChange A A[X] S (s ⊗ₜ[A[X]] KaehlerDifferential.D A A[X] X) =
      s • KaehlerDifferential.D A S (algebraMap A[X] S X) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

end EtaleCoordinate
end AlgebraicCurves.Foundations.Algebra.Proofs.FormallySmoothEvaluation

namespace Algebra.FormallySmooth

open _root_.AlgebraicCurves.Foundations.Algebra.Proofs.FormallySmoothEvaluation
open _root_.Polynomial
universe u v


theorem formallySmooth_and_formallyUnramified_aeval_of_existsUnique_smul_D_eq
    {A : Type u} {S : Type v} [CommRing A] [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (ht : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallySmooth ∧
      (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.FormallyUnramified := by
  let alg : Algebra A[X] S := (Polynomial.aeval t : A[X] →ₐ[A] S).toRingHom.toAlgebra
  have halg : ∀ p : A[X], algebraMap A[X] S p = aeval t p := fun _ => rfl
  have : IsScalarTower A A[X] S := IsScalarTower.of_algebraMap_eq fun a => by
    rw [halg, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, aeval_C]
  have hX : algebraMap A[X] S X = t := by rw [halg, aeval_X]
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A A[X] S) := by
    intro z₁ z₂ h
    obtain ⟨s₁, rfl⟩ := EtaleCoordinate.exists_eq_tmul_D_X z₁
    obtain ⟨s₂, rfl⟩ := EtaleCoordinate.exists_eq_tmul_D_X z₂
    rw [EtaleCoordinate.mapBaseChange_tmul_D_X, EtaleCoordinate.mapBaseChange_tmul_D_X, hX] at h
    obtain ⟨s, _, hs⟩ := ht (s₁ • KaehlerDifferential.D A S t)
    have e1 : s₁ = s := hs s₁ rfl
    have e2 : s₂ = s := hs s₂ h
    rw [e1, e2]
  have hsurj : Function.Surjective (KaehlerDifferential.mapBaseChange A A[X] S) := by
    intro ω
    obtain ⟨s, hs, -⟩ := ht ω
    exact ⟨s ⊗ₜ KaehlerDifferential.D A A[X] X, by
      rw [EtaleCoordinate.mapBaseChange_tmul_D_X, hX, hs]⟩
  have hΩ : Subsingleton (Ω[S⁄A[X]]) := by
    refine ⟨fun ω₁ ω₂ => ?_⟩
    have hzero : ∀ ω : Ω[S⁄A[X]], ω = 0 := by
      intro ω
      obtain ⟨ω', rfl⟩ := KaehlerDifferential.map_surjective A A[X] S ω
      obtain ⟨z, rfl⟩ := hsurj ω'
      exact (KaehlerDifferential.exact_mapBaseChange_map A A[X] S).apply_apply_eq_zero z
    rw [hzero ω₁, hzero ω₂]
  have hH1 : Subsingleton (Algebra.H1Cotangent A[X] S) := by
    refine ⟨fun h₁ h₂ => ?_⟩
    have hδ : ∀ h : Algebra.H1Cotangent A[X] S, Algebra.H1Cotangent.δ A A[X] S h = 0 := by
      intro h
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A A[X] S).apply_apply_eq_zero h
    have hzero : ∀ h : Algebra.H1Cotangent A[X] S, h = 0 := by
      intro h
      obtain ⟨h', rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ A A[X] S) h).mp (hδ h)
      rw [Subsingleton.elim h' 0, map_zero]
    rw [hzero h₁, hzero h₂]
  have : Algebra.FormallyEtale A[X] S := ⟨hΩ, hH1⟩
  exact ⟨(inferInstance : Algebra.FormallySmooth A[X] S), (inferInstance :
    Algebra.FormallyUnramified A[X] S)⟩
end Algebra.FormallySmooth
end ProofImplementation
