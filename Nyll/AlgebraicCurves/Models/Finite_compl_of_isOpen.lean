/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_compl_of_isOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Finite compl of isOpen

The complement of an open subset of a curve is finite when the open contains the generic point.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.Finite_compl_of_isOpen

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

theorem _root_.AlgebraicCurve.finite_compl_of_isOpen
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) (hU : (U : Set C).Nonempty) :
    ((U : Set C)ᶜ).Finite := by
  classical
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  have : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have : IsNoetherian C := ⟨⟩
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hcl : ∀ x ∈ (U : Set C)ᶜ, IsClosed ({x} : Set C) := fun x hx =>
    AlgebraicCurve.isClosed_singleton_of_ne_genericPoint c x (by rintro rfl; exact hx hη)
  obtain ⟨S, hSfin, hSclosed, hSirr, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  rw [hSU]
  refine hSfin.sUnion fun t ht => ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint (hSclosed t ht)
  set w := (hSirr t ht).genericPoint
  have hwU : w ∈ (U : Set C)ᶜ := by
    rw [hSU]; exact Set.mem_sUnion_of_mem hgen.mem ht
  have ht1 : t = {w} := by
    rw [← hgen.def, (hcl w hwU).closure_eq]
  rw [ht1]
  exact Set.finite_singleton w
end AlgebraicCurves.Models.Proofs.Finite_compl_of_isOpen
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp] AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec
