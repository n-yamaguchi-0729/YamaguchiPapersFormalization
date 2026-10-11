/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Fibre
import AlgebraicCurves.Geometry.Schemes.SchemeFibreEndo
import AlgebraicCurves.Geometry.Schemes.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.abelianSchemePropertyBundle_fibreStr
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_fibre_mul_comm
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_isUnit
import AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle

/-!
# Relative Group Law is Finite and flat scheme Nsmul of is Unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem _root_.GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) := by
  have : IsProper f := hJ.proper
  have hlqf : LocallyQuasiFinite (L.schemeNsmul n) := by
    refine AlgebraicGeometry.locallyQuasiFinite_of_forall_locallyQuasiFinite_schemeFibreEndo f
      (L.schemeNsmul n) (L.schemeNsmul_over n) ?_
    intro s
    rw [← RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo L s n]
    have hfib := GoodReductionJacobian.abelianSchemePropertyBundle_fibreStr hJ s
    have : Smooth (RelativeGroupLaw.fibreStr f s) := hfib.smooth
    have : LocallyOfFiniteType (RelativeGroupLaw.fibreStr f s) := inferInstance
    have hu : IsUnit ((n : ℕ) : RelativeGroupLaw.baseResidueField s) := by
      have h := hn.map (((Spec (CommRingCat.of R)).Γevaluation s).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      simpa only [map_natCast] using h
    exact RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_isUnit (L.fibre s)
      (fun t' x y => RelativeGroupLaw.fibre_mul_comm L hcomm s t' x y) n hu
  have := hlqf
  have : IsProper (L.schemeNsmul n) := by
    have : IsProper (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]; infer_instance
    exact IsProper.of_comp _ f
  have hfin : IsFinite (L.schemeNsmul n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  refine ⟨hfin, ?_⟩
  exact RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle L hJ n hfin
end RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
end ProofImplementation

attribute [-simp] GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply
