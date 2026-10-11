/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_geometricallyIntegral
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_of_isPullback
import AlgebraicCurves.Geometry.Schemes.bijective_algebraMap_appTop_of_isProper_of_isIntegral
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat

/-!
# Abelian Scheme Property Bundle bijective app Top fibre of is Pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
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
attribute [-simp] AlgebraicGeometry.schemeFibreEndo_fst

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem
  _root_.GoodReductionJacobian.AbelianSchemePropertyBundle.bijective_appTop_fibre_of_isPullback
    {T : Type u} [CommRing T] {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of T)}
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {k : Type u} [Field k] (ρ : T →+* k)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of k)) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fk.appTop).hom := by
  have hk : AbelianSchemePropertyBundle k fk := h₀.of_isPullback hi₀
  have : IsProper fk := hk.proper
  have : GeometricallyIntegral fk := hk.geometricallyIntegral
  have : CompactSpace ↥Ak := QuasiCompact.compactSpace_of_compactSpace fk
  have : QuasiSeparatedSpace ↥Ak := (quasiSeparated_iff_quasiSeparatedSpace fk).mp inferInstance
  apply AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat fk
    (AlgebraicClosure k)
  have : IsIntegral (pullback fk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure
    k))))) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd fk _)
  exact AlgebraicGeometry.bijective_algebraMap_appTop_of_isProper_of_isIntegral (AlgebraicClosure
    k) (pullback.snd fk _)

end AbelianSchemePropertyBundle_bijective_appTop_fibre_of_isPullback
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation
