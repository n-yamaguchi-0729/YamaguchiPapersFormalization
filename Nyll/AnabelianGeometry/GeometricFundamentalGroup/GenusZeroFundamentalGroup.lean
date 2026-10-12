/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalFundamentalGroup
import Nyll.AlgebraicCurves.Places.Exists_place_notMem_ord_neg_and_forall_ord_eq_one
import Nyll.AlgebraicCurves.Models.CurveModel_exists_curveModel_iso_of_algEquiv
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!+# The étale fundamental group of a proper genus-zero curve

We construct two distinct places and a generating rational parameter from the genus-zero
hypothesis. The resulting function-field isomorphism gives an actual rational curve model.
Pullback along the model isomorphism transports the proved rational-curve fundamental-group
theorem to the original curve and its original geometric point.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- A genus-zero curve function field over an algebraically closed field of characteristic zero
is isomorphic to the rational function field, without chosen places or a chosen parameter. -/
theorem nonempty_ratFunc_algEquiv_of_genus_zero (hg : genusFF K F = 0) :
    Nonempty (RatFunc K ≃ₐ[K] F) := by
  classical
  obtain ⟨v₀, _, _, _⟩ :=
    exists_place_notMem_ord_neg_and_forall_ord_eq_one (K := K) (F := F) ∅
  obtain ⟨vInfty, _, hnot, _⟩ :=
    exists_place_notMem_ord_neg_and_forall_ord_eq_one (K := K) (F := F) {v₀}
  have hne : v₀ ≠ vInfty := by
    intro h
    exact hnot (Finset.mem_singleton.mpr h.symm)
  obtain ⟨t, _, htr, hgen, _⟩ := exists_parameter_of_genus_zero hg v₀ vInfty hne
  exact ⟨(RatFunc.algEquivOfTranscendental t htr).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)⟩

/-- The actual étale fundamental group of a proper genus-zero curve model is trivial at every
geometric point over a separably closed field. No rational coordinate or model is assumed. -/
theorem subsingleton_fundamentalGroup_of_genus_zero (M : CurveModel K F)
    (hg : genusFF K F = 0) {Ω : Type} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ M.C) : Subsingleton π₁ᵉᵗ(ξ) := by
  obtain ⟨e⟩ := nonempty_ratFunc_algEquiv_of_genus_zero hg
  obtain ⟨N, i, _⟩ := CurveModel.exists_curveModel_iso_of_algEquiv e.symm M
  let E : FiniteEtale N.C ≌ FiniteEtale M.C :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i
  have pullbackEquivalence : (pullback i.inv).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ i.inv) :=
    fundamentalGroupEquivOfPullbackEquivalence i.inv ξ
  have singleton : Subsingleton π₁ᵉᵗ(ξ ≫ i.inv) :=
    subsingleton_fundamentalGroup_rational N (ξ ≫ i.inv)
  exact ⟨fun σ τ => eπ.injective (Subsingleton.elim (eπ σ) (eπ τ))⟩

end AnabelianGeometry.GeometricFundamentalGroup
