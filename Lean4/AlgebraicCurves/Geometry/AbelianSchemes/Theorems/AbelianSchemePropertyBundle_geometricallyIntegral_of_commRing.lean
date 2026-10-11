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

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Geometrically.Basic
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_baseChange_of_field
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral

/-!
# Abelian Scheme Property Bundle geometrically Integral of comm Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral_of_commRing
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) : GeometricallyIntegral f := by
  rw [geometricallyIntegral_iff]
  intro K _ y Z fst snd hpb
  have hK : AbelianSchemePropertyBundle K (pullback.snd f y) :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.baseChange_of_field hA y
  have hgi : GeometricallyIntegral (pullback.snd f y) :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.geometricallyIntegral hK
  have : IsIntegral (Limits.pullback f y) := self_of_isIntegral_of_geometrically hgi.1
  exact IsIntegral.of_isIso hpb.isoPullback.inv
end AbelianSchemePropertyBundle_geometricallyIntegral_of_commRing
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
