/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Schemes.Smooth_isRegularLocalRing_stalk
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_isIntegral_of_field
import AlgebraicCurves.Geometry.Schemes.ringKrullDim_stalk_eq_of_isFinite_endomorphism
import AlgebraicCurves.Geometry.Schemes.IsFinite_ringKrullDim_stalk_quotient_eq_zero
import AlgebraicCurves.Foundations.CommutativeAlgebra.Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero

/-!
# Abelian Scheme Property Bundle flat of is Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_flat_of_isFinite
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mIsogFlat

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

private theorem isLocallyNoetherian (hA : AbelianSchemePropertyBundle K f) : IsLocallyNoetherian A
  := by
  have : Smooth f := hA.smooth
  exact LocallyOfFiniteType.isLocallyNoetherian f


theorem flat_stalkMap (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f)
    [IsFinite β.1] (x : A) : (β.1.stalkMap x).hom.Flat := by
  have : Smooth f := hA.smooth
  have : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  have : IsLocallyNoetherian A := isLocallyNoetherian hA
  have hx : IsRegularLocalRing (A.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := f) x
  have hy : IsRegularLocalRing (A.presheaf.stalk (β.1.base x)) :=
    Smooth.isRegularLocalRing_stalk (f := f) (β.1.base x)
  let alg : Algebra (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    (β.1.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (β.1.stalkMap x).hom)
  have hfib : ringKrullDim ((A.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (β.1.base x))).map
        (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero β.1 x
  have hdim : ringKrullDim (A.presheaf.stalk x) =
      ringKrullDim (A.presheaf.stalk (β.1.base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism (f := f) β.1 β.2 x
  have hflat : Module.Flat (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) hfib hdim
  exact hflat

theorem main (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  Flat.of_stalkMap β.1 (flat_stalkMap hA β)

end P2mIsogFlat

theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.flat_of_isFinite
    (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  P2mIsogFlat.main hA β

end
end AbelianSchemePropertyBundle_flat_of_isFinite
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-instance] instTopologicallyFGOfFiniteType
