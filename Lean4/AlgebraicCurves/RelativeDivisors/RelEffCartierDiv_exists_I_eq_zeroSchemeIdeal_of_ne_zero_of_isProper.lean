/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.RingTheory.FinitePresentation
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal
import AlgebraicCurves.Geometry.Schemes.isReduced_of_smooth_over_field
import AlgebraicCurves.Models.Finite_compl_of_isOpen

/-!
Construct a relative effective Cartier divisor from a nonzero section in the proper case.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
attribute [-instance]
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instSMulAlgEquiv
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instMulActionAlgEquiv
  AlgebraicCurve.Pic0.instSMulAlgEquiv
  AlgebraicCurve.CurveModel.isProper
  AlgebraicCurve.CurveModel.isIntegral
  AlgebraicCurve.CurveModel.smooth
attribute [-simp]
  AlgebraicCurve.Place.mk.injEq
  AlgebraicCurve.Divisor.degree_single
  AlgebraicCurve.Divisor.smul_single
  AlgebraicCurve.Place.smul_toValuationSubring
  AlgebraicCurve.Place.heightOneSpectrum_asIdeal
  AlgebraicCurve.Place.coe_algebraMap
  AlgebraicCurve.Place.ord_one
  AlgebraicCurve.Place.coe_smulRingEquiv_apply
  AlgebraicCurve.Pic0.coe_degZeroSMulHom
  AlgebraicCurve.Place.deg_smul
  AlgebraicCurve.Pic0.mk_zero
  AlgebraicCurve.Place.mk.sizeOf_spec
  AlgebraicCurve.Divisor.degree_smul
  AlgebraicCurve.Pic0.mk_add
  AlgebraicCurve.Place.ord_zero
  AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring
  AlgebraicCurve.CurveModel.mk.injEq
  AlgebraicCurve.CurveModel.mk.sizeOf_spec

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
      [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = Scheme.Modules.zeroSchemeIdeal s := by
  classical
  let C : Scheme.{u} := pullback f x
  let c : C ⟶ Spec (CommRingCat.of k) := pullback.snd f x
  have : IsProper c := inferInstance
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 c :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (g : X ⟶ Y) => SmoothOfRelativeDimension 1 g)
      (IsPullback.of_hasPullback f x) inferInstance
  have : QuasiCompact c := inferInstance
  have : IrreducibleSpace ↥C :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) x (pullback.fst f x) c
      (IsPullback.of_hasPullback f x)
  have : IsReduced C :=
    isReduced_of_smooth_over_field (g := c) (SmoothOfRelativeDimension.smooth 1 c)
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced _
  let I : C.IdealSheafData := Scheme.Modules.zeroSchemeIdeal s
  let g : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ c
  have hη : genericPoint C ∉ I.support :=
    Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal hM s hs
  have hfin : (I.support : Set C).Finite := by
    have h := AlgebraicCurve.finite_compl_of_isOpen c I.support.compl ⟨genericPoint _, hη⟩
    simpa [TopologicalSpace.Closeds.coe_compl, compl_compl] using h
  have : Finite ↥(I.subscheme) := by
    have : Finite (I.support : Set C) := hfin.to_subtype
    refine Finite.of_injective (fun z => (⟨I.subschemeι.base z, ?_⟩ : (I.support : Set C))) ?_
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · intro a b hab
      exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)
  have : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun y => Set.toFinite _
  have : IsProper g := inferInstance
  have hgfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  have : Flat g := inferInstance
  have hlofp : LocallyOfFinitePresentation g := by
    have : IsAffine I.subscheme := isAffine_of_isAffineHom g
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    have hft : g.appTop.hom.Finite :=
      g.finite_appTop
    let := g.appTop.hom.toAlgebra
    have : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(I.subscheme, ⊤) := hft
    have : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of
        k)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨t₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨g.finrank t₀, ⟨I, hgfin, inferInstance, hlofp, fun t => ?_⟩, rfl⟩
  rw [Subsingleton.elim t t₀]
end RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
