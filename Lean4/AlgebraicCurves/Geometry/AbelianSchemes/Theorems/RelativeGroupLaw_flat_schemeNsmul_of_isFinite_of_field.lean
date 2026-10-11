/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import AlgebraicCurves.Foundations.CommutativeAlgebra.Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import AlgebraicCurves.Geometry.Schemes.IsFinite_ringKrullDim_stalk_quotient_eq_zero
import AlgebraicCurves.Geometry.Schemes.ringKrullDim_stalk_eq_of_isFinite_endomorphism
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_isIntegral_of_field

/-!
# Relative Group Law flat scheme Nsmul of is Finite of field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_field
    {k : Type u} [Field k] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of k)}
    (L : RelativeGroupLaw k f) (hJ : AbelianSchemePropertyBundle k f)
    (n : ℕ) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by
  have := hJ.smooth
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have hnoeth : IsLocallyNoetherian J := LocallyOfFiniteType.isLocallyNoetherian f
  have hint : IsIntegral J := hJ.isIntegral_of_field
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  algebraize [((L.schemeNsmul n).stalkMap x).hom]
  have : IsRegularLocalRing (J.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
  have : IsRegularLocalRing (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) ((L.schemeNsmul n).base x)
  have : IsNoetherianRing (J.presheaf.stalk x) := inferInstance
  have : IsLocalHom (algebraMap
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((L.schemeNsmul n).stalkMap x).hom)
  have hfib : ringKrullDim (↑(J.presheaf.stalk x) ⧸
      (maximalIdeal ↑(J.presheaf.stalk ((L.schemeNsmul n).base x))).map
        (algebraMap ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero (L.schemeNsmul n) x
  have hdim : ringKrullDim (J.presheaf.stalk x) =
      ringKrullDim (J.presheaf.stalk ((L.schemeNsmul n).base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism
      (f := f) (L.schemeNsmul n) (L.schemeNsmul_over n) x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      ↑(J.presheaf.stalk ((L.schemeNsmul n).base x)) ↑(J.presheaf.stalk x) hfib hdim
end RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_field
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-instance] instTopologicallyFGOfFiniteType
