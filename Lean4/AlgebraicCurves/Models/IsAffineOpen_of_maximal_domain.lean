/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isAffineOpen_of_maximal_domain.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Geometry.Schemes.Scheme_Opens_isProper_toSpecPolynomial_of_maximal
import AlgebraicCurves.Geometry.Schemes.Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
import AlgebraicCurves.Geometry.Schemes.valuationRing_stalk_of_smoothOfRelativeDimension_one

/-!
# IsAffineOpen of maximal domain

The maximal domain of a nonconstant function on a proper smooth integral curve is an affine open.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.IsAffineOpen_of_maximal_domain

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Polynomial

theorem _root_.AlgebraicCurve.isAffineOpen_of_maximal_domain
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by
  let φ : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
    (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso
        (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))
  have : IsProper φ := Scheme.Opens.isProper_toSpecPolynomial_of_maximal c
    (valuationRing_stalk_of_smoothOfRelativeDimension_one c) U s hU
  have : LocallyQuasiFinite φ := LocallyQuasiFinite.of_finite_preimage_singleton φ
    (Scheme.Opens.finite_preimage_singleton_toSpecPolynomial c U s hs)
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  exact isAffine_of_isAffineHom φ
end AlgebraicCurves.Models.Proofs.IsAffineOpen_of_maximal_domain
end ProofImplementation
