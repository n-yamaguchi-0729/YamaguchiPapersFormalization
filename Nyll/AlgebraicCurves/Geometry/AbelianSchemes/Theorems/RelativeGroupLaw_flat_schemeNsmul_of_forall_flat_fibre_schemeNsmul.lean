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

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Fibre
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeFibreEndo
import Nyll.AlgebraicCurves.Geometry.Schemes.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo

/-!
# Relative Group Law flat scheme Nsmul of forall flat fibre scheme Nsmul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian


theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [Flat f] [LocallyOfFinitePresentation f] (G : RelativeGroupLaw R f) (n : ℕ)
    (hfib : ∀ s : (Spec (CommRingCat.of R) : Scheme.{u}), Flat ((G.fibre s).schemeNsmul n)) :
    Flat (G.schemeNsmul n) := by
  apply AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo f
    (G.schemeNsmul n) (G.schemeNsmul_over n)
  intro s
  rw [← GoodReductionJacobian.RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo]
  exact hfib s
end RelativeGroupLaw_flat_schemeNsmul_of_forall_flat_fibre_schemeNsmul
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
