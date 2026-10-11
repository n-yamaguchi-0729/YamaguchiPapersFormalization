/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_isLocallyConstant_fibreEulerChar.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.MumfordTruncation
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_finite_K0
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_flat_K0
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_bijective_kerMapBaseChange
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Mumford_bijective_cokerMapBaseChange
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-!
Local constancy of the fibre kernel-minus-cokernel dimension of a finite flat two-term model.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_isLocallyConstant_fibreEulerChar

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
open _root_.TwoChartCech
namespace Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]

theorem finrank_ker_sub_finrank_coker {K : Type u} [Field K] {V W : Type u} [AddCommGroup V]
    [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W] (f : V →ₗ[K] W) :
    (Module.finrank K (LinearMap.ker f) : ℤ) - Module.finrank K (W ⧸ LinearMap.range f)
      = (Module.finrank K V : ℤ) - Module.finrank K W := by
  have h1 := f.finrank_range_add_finrank_ker
  have h2 := (LinearMap.range f).finrank_quotient_add_finrank
  omega

theorem fibreEulerChar_eq_of_bijective [Module.Flat R C0] [Module.Flat R C1] [IsNoetherianRing R]
    [Module.Finite R (LinearMap.ker d)] (𝔭 : PrimeSpectrum R)
    (hker : Function.Bijective
      (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) 𝔭.asIdeal.ResidueField))
    (hcoker : Function.Bijective
      (cokerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) 𝔭.asIdeal.ResidueField)) :
    (Module.finrank 𝔭.asIdeal.ResidueField
        (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ)
      - Module.finrank 𝔭.asIdeal.ResidueField
          ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange 𝔭.asIdeal.ResidueField))
    = (Module.rankAtStalk (K0 d) 𝔭 : ℤ) - Module.rankAtStalk (Fin (rank d) → R) 𝔭 := by
  have := finite_K0 d; have := flat_K0 d
  rw [← (LinearEquiv.ofBijective _ hker).finrank_eq, ← (LinearEquiv.ofBijective _
    hcoker).finrank_eq,
    finrank_ker_sub_finrank_coker, Module.rankAtStalk_eq, Module.rankAtStalk_eq]

end TwoChartCech.Mumford

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.TwoChartCech TwoChartCech_isLocallyConstant_fibreEulerChar.TwoChartCech
  _root_.TwoChartCech.Mumford TwoChartCech_isLocallyConstant_fibreEulerChar.TwoChartCech.Mumford
  in
theorem _root_.TwoChartCech.isLocallyConstant_fibreEulerChar
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1] (d : C0 →ₗ[R] C1)
    [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    IsLocallyConstant fun 𝔭 : PrimeSpectrum R =>
      (Module.finrank 𝔭.asIdeal.ResidueField
          (LinearMap.ker (d.baseChange 𝔭.asIdeal.ResidueField)) : ℤ)
        - Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[R] C1) ⧸ LinearMap.range (d.baseChange
              𝔭.asIdeal.ResidueField)) := by
  have := Mumford.finite_K0 d; have := Mumford.flat_K0 d
  have : Module.FinitePresentation R (Mumford.K0 d) := Module.finitePresentation_of_finite R _
  have h0 : IsLocallyConstant (Module.rankAtStalk (R := R) (Mumford.K0 d)) :=
    Module.isLocallyConstant_rankAtStalk
  have h1 : IsLocallyConstant (Module.rankAtStalk (R := R) (Fin (Mumford.rank d) → R)) :=
    Module.isLocallyConstant_rankAtStalk
  have h := (h0.prodMk h1).comp (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
  convert h using 1
  funext 𝔭
  exact Mumford.fibreEulerChar_eq_of_bijective d 𝔭 (Mumford.bijective_kerMapBaseChange d _)
    (Mumford.bijective_cokerMapBaseChange d _)

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_isLocallyConstant_fibreEulerChar
end ProofImplementation

attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq
