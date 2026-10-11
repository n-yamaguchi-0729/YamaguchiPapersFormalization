/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Foundations.CommutativeAlgebra.RingHom_existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_span_pair
import AlgebraicCurves.Foundations.Algebra.RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D

/-!
# Ring Hom formally Smooth and formally Unramified eval2 Ring Hom of maximal Ideal eq span
pair
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair

open IsLocalRing

open _root_.RingHom
  (existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_span_pair) in
theorem
  _root_.RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (i : A →+* S) (hi : i.FormallySmooth) (hif : i.EssFiniteType)
    (hres : Function.Surjective ((IsLocalRing.residue S).comp i))
    (t : S) (hm : maximalIdeal S = Ideal.span {i ϖ, t}) (ht : t ∉ Ideal.span {i ϖ}) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified
      ∧
      (Polynomial.eval₂RingHom i t).EssFiniteType := by
  classical
  have hCt : ∀ a : A, Polynomial.eval₂RingHom i t (Polynomial.C a) = i a := fun a => by simp
  have hef : (Polynomial.eval₂RingHom i t).EssFiniteType := by
    let algS : Algebra A S := i.toAlgebra
    let algPS : Algebra (Polynomial A) S := (Polynomial.eval₂RingHom i t).toAlgebra
    have : IsScalarTower A (Polynomial A) S :=
      IsScalarTower.of_algebraMap_eq (fun a => (hCt a).symm)
    have : Algebra.EssFiniteType A S := hif
    exact Algebra.EssFiniteType.of_comp A (Polynomial A) S
  have hK :=
    existsUnique_eq_smul_kaehlerDifferential_D_of_formallySmooth_of_maximalIdeal_eq_span_pair
      ϖ hϖ i hi hif hres t hm ht
  obtain ⟨hJs, hJu⟩ :=
    RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D i hi t hK
  exact ⟨hJs, hJu, hef⟩
end RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
