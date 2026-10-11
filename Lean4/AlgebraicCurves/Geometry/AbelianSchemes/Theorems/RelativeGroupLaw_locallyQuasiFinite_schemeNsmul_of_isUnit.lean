/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Morphisms.QuasiFinite
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel

/-!
# Relative Group Law locally Quasi Finite scheme Nsmul of is Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit
    {R : Type u} [Field R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [LocallyOfFiniteType f] (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    LocallyQuasiFinite (G.schemeNsmul n) := by
  have : FormallyUnramified (G.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero G hcomm n
      (fun R' S' φ hφ hker t k hk hnk =>
        GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit
          G n hn R' S' φ hφ hker t k hk hnk)
  have : LocallyOfFiniteType (G.schemeNsmul n) := by
    have h : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by
      rw [G.schemeNsmul_over]
      infer_instance
    exact AlgebraicGeometry.locallyOfFiniteType_of_comp (G.schemeNsmul n) f
  exact AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType _
end RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
