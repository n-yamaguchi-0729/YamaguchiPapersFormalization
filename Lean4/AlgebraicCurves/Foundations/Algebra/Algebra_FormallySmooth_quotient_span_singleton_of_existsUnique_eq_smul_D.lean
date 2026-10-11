/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Foundations.Algebra.RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D

/-!
# Algebra Formally Smooth quotient span singleton of exists Unique eq smul D
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D

open Polynomial

theorem _root_.Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D
    {A : Type} [CommRing A] {S : Type} [CommRing S] [Algebra A S] [Algebra.FormallySmooth A S]
    (t : S) (hdt : ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    Algebra.FormallySmooth A (S ⧸ Ideal.span ({t} : Set S)) := by
  classical
  set J : Ideal S := Ideal.span ({t} : Set S) with hJ
  have hinst : (algebraMap A S).toAlgebra = ‹Algebra A S› := Algebra.algebra_ext _ _ (fun _ => rfl)
  have hi : (algebraMap A S).FormallySmooth := RingHom.formallySmooth_algebraMap.mpr ‹_›
  have hdt' : letI : Algebra A S := (algebraMap A S).toAlgebra;
      ∀ ω : Ω[S⁄A], ∃! s : S, ω = s • KaehlerDifferential.D A S t := by
    rw [hinst]; exact hdt
  obtain ⟨hfs, -⟩ :=
    RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    (algebraMap A S) hi t hdt'
  let e : Polynomial A →+* S := Polynomial.eval₂RingHom (algebraMap A S) t
  let algXS : Algebra (Polynomial A) S := e.toAlgebra
  have : IsScalarTower A (Polynomial A) S := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A S a = e (Polynomial.C a)
    simp [e, Polynomial.eval₂RingHom])
  have hFS : Algebra.FormallySmooth (Polynomial A) S := hfs
  have heX : algebraMap (Polynomial A) S Polynomial.X = t := by
    change e Polynomial.X = t; simp [e, Polynomial.eval₂RingHom]
  refine Algebra.FormallySmooth.of_comp_surjective ?_
  intro B _ _ I hI g
  let algXB : Algebra (Polynomial A) B := (Polynomial.aeval (0 : B)).toRingHom.toAlgebra
  have : IsScalarTower A (Polynomial A) B := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A B a = (Polynomial.aeval (0 : B)) (Polynomial.C a)
    simp)
  have hXB : algebraMap (Polynomial A) B Polynomial.X = 0 := by
    change (Polynomial.aeval (0 : B)) Polynomial.X = 0; simp
  have hcomm : ∀ p : Polynomial A,
      g (Ideal.Quotient.mk J (algebraMap (Polynomial A) S p)) = Ideal.Quotient.mk I (algebraMap
        (Polynomial A) B p) := by
    intro p
    have h1 : Ideal.Quotient.mk J (algebraMap (Polynomial A) S p) = algebraMap A (S ⧸ J) (p.coeff
      0) := by
      change Ideal.Quotient.mk J (Polynomial.eval₂ (algebraMap A S) t p) = _
      rw [Polynomial.hom_eval₂, show Ideal.Quotient.mk J t = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl), Polynomial.eval₂_at_zero]
      rfl
    have h2 : algebraMap (Polynomial A) B p = algebraMap A B (p.coeff 0) := by
      change (Polynomial.aeval (0 : B)) p = _
      rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    rw [h1, h2, AlgHom.commutes]; rfl
  let g' : S →ₐ[Polynomial A] B ⧸ I :=
    { toRingHom := g.toRingHom.comp (Ideal.Quotient.mk J)
      commutes' := fun p => by
        change g (Ideal.Quotient.mk J (algebraMap (Polynomial A) S p)) = Ideal.Quotient.mk I
          (algebraMap (Polynomial A) B p)
        exact hcomm p }
  obtain ⟨h, hh⟩ := Algebra.FormallySmooth.comp_surjective (Polynomial A) S I hI g'
  have hht : h t = 0 := by rw [← heX, AlgHom.commutes, hXB]
  have hker : ∀ j ∈ J, (h.restrictScalars A) j = 0 := by
    intro j hj
    rw [hJ, Ideal.mem_span_singleton] at hj
    obtain ⟨s, rfl⟩ := hj
    change h (t * s) = 0
    rw [map_mul, hht, zero_mul]
  let hbar : (S ⧸ J) →ₐ[A] B := Ideal.Quotient.liftₐ J (h.restrictScalars A) hker
  refine ⟨hbar, ?_⟩
  apply AlgHom.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I (hbar (Ideal.Quotient.mk J s)) = g (Ideal.Quotient.mk J s)
  have : hbar (Ideal.Quotient.mk J s) = h s := rfl
  rw [this]
  exact congrArg (fun φ : S →ₐ[Polynomial A] B ⧸ I => φ s) hh
end Algebra_FormallySmooth_quotient_span_singleton_of_existsUnique_eq_smul_D
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
