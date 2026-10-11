/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import AlgebraicCurves.Geometry.Schemes.SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed

/-!
# Proper integral smooth curves are not affine

A proper integral scheme smooth of relative dimension one over a field cannot be affine.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace not_isAffine_of_isProper_of_smoothOfRelativeDimension_one

open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

theorem _root_.AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by
  intro hX
  have : IsAffineHom f := isAffineHom_of_isAffine f
  have hfin : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hΓ : (f.appTop).hom.Finite := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  let φ : k →+* Γ(X, ⊤) := (f.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφfin : φ.Finite :=
    RingHom.Finite.comp hΓ (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfield : IsField Γ(X, ⊤) := by
    let := φ.toAlgebra
    have : Module.Finite k Γ(X, ⊤) := hφfin
    have : Algebra.IsIntegral k Γ(X, ⊤) := Algebra.IsIntegral.of_finite k _
    exact (Algebra.IsIntegral.isField_iff_isField (R := k) (S := Γ(X, ⊤)) φ.injective).mp
      (Field.toIsField k)
  have hsub : Subsingleton (PrimeSpectrum Γ(X, ⊤)) := by
    have := Ring.isField_iff_isSimpleOrder_ideal.mp hfield
    refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
    rcases IsSimpleOrder.eq_bot_or_eq_top p.asIdeal with hp | hp
    · rcases IsSimpleOrder.eq_bot_or_eq_top q.asIdeal with hq | hq
      · rw [hp, hq]
      · exact absurd hq q.isPrime.ne_top
    · exact absurd hp p.isPrime.ne_top
  have hsubX : Subsingleton X := by
    have : Subsingleton (Spec Γ(X, ⊤)) := hsub
    exact (Scheme.homeoOfIso X.isoSpec).toEquiv.subsingleton
  have hclosed : IsClosed ({genericPoint X} : Set X) := by
    have : ({genericPoint X} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    rw [this]; exact isClosed_univ
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk (genericPoint X)) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed f
      (genericPoint X) hclosed
  exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk (genericPoint X))
    (Field.toIsField X.functionField)
end not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
