/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified
import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange

/-!
# Ring Hom formally Smooth and formally Unramified eval2 Ring Hom of exists Unique eq smul D
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D

open Polynomial

theorem _root_.RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    {A S : Type} [CommRing A] [CommRing S] (i : A →+* S) (hi : i.FormallySmooth) (t : S)
    (hdt : letI : Algebra A S := i.toAlgebra;
      ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified
      := by
  let algS : Algebra A S := i.toAlgebra
  let inst : Algebra A[X] S := (Polynomial.eval₂RingHom i t).toAlgebra
  have halg : ∀ P : A[X], algebraMap A[X] S P = Polynomial.eval₂RingHom i t P := fun _ => rfl
  have hst : IsScalarTower A A[X] S := IsScalarTower.of_algebraMap_eq fun r => by
    rw [halg, Polynomial.algebraMap_apply]
    change i r = Polynomial.eval₂RingHom i t (Polynomial.C r)
    simp
  have : Algebra.FormallySmooth A S := hi
  have hX : algebraMap A[X] S X = t := by rw [halg]; simp
  have hmapDX : KaehlerDifferential.map A A A[X] S (KaehlerDifferential.D A A[X] X) =
    KaehlerDifferential.D A S t := by
    rw [KaehlerDifferential.map_D, hX]
  have hω : ∀ ω : Ω[A[X]⁄A], ω = (KaehlerDifferential.polynomialEquiv A ω) • KaehlerDifferential.D
    A A[X] X := fun ω => by
    rw [← KaehlerDifferential.polynomialEquiv_symm, LinearEquiv.symm_apply_apply]
  have hrep : ∀ x : TensorProduct A[X] S (Ω[A[X]⁄A]), ∃ s : S, x = s ⊗ₜ[A[X]] KaehlerDifferential.D
    A A[X] X := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s ω =>
      refine ⟨(KaehlerDifferential.polynomialEquiv A ω) • s, ?_⟩
      rw [TensorProduct.smul_tmul, ← hω ω]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by rw [TensorProduct.add_tmul]⟩
  have hbij : Function.Bijective (KaehlerDifferential.mapBaseChange A A[X] S) := by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hrep x
      obtain ⟨b, rfl⟩ := hrep y
      rw [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.mapBaseChange_tmul, hmapDX]
        at hxy
      obtain ⟨s, -, hs⟩ := hdt (a • KaehlerDifferential.D A S t)
      rw [hs a rfl, hs b hxy]
    · intro ω
      obtain ⟨s, hs, -⟩ := hdt ω
      exact ⟨s ⊗ₜ[A[X]] KaehlerDifferential.D A A[X] X,
        by rw [KaehlerDifferential.mapBaseChange_tmul, hmapDX, hs]⟩
  have hfe : Algebra.FormallyEtale A[X] S :=
    Algebra.FormallyEtale.of_formallySmooth_of_bijective_mapBaseChange hbij
  have h1 : Algebra.FormallySmooth A[X] S := inferInstance
  have h2 : Algebra.FormallyUnramified A[X] S := inferInstance
  exact ⟨h1, h2⟩
end RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
