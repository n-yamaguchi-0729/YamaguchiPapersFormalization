/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Tactic.Algebraize
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import AlgebraicCurves.Foundations.CommutativeAlgebra.Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import AlgebraicCurves.Geometry.Schemes.LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero
import AlgebraicCurves.Geometry.Schemes.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
import AlgebraicCurves.Geometry.Schemes.isIntegral_of_smooth_of_preconnectedSpace

/-!
# Relative Group Law flat scheme Nsmul of locally Quasi Finite of field
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

open IsLocalRing

theorem
  _root_.GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_locallyQuasiFinite_of_field
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace A]
    (G : RelativeGroupLaw k f) (n : ℕ) [LocallyQuasiFinite (G.schemeNsmul n)] :
    Flat (G.schemeNsmul n) := by
  have : LocallyOfFiniteType f := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  have hnoeth : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  have : Nonempty A := ⟨x⟩
  have hint : IsIntegral A := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  algebraize [((G.schemeNsmul n).stalkMap x).hom]
  have : IsRegularLocalRing (A.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
  have : IsRegularLocalRing (A.presheaf.stalk ((G.schemeNsmul n).base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) ((G.schemeNsmul n).base x)
  have : IsNoetherianRing (A.presheaf.stalk x) := inferInstance
  have : IsLocalHom (algebraMap
      ↑(A.presheaf.stalk ((G.schemeNsmul n).base x)) ↑(A.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom ((G.schemeNsmul n).stalkMap x).hom)
  have hfib : ringKrullDim (↑(A.presheaf.stalk x) ⧸
      (maximalIdeal ↑(A.presheaf.stalk ((G.schemeNsmul n).base x))).map
        (algebraMap ↑(A.presheaf.stalk ((G.schemeNsmul n).base x)) ↑(A.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero (G.schemeNsmul n) x
  have hdim : ringKrullDim (A.presheaf.stalk x) =
      ringKrullDim (A.presheaf.stalk ((G.schemeNsmul n).base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
      (f := f) (G.schemeNsmul n) (G.schemeNsmul_over n) x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (A.presheaf.stalk ((G.schemeNsmul n).base x)) (A.presheaf.stalk x) hfib hdim
end RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-instance] instTopologicallyFGOfFiniteType
