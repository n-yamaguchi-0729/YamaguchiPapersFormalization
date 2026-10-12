/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalPuncturedChart
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.GenusZeroParameter
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AffineLineFundamentalGroup
import Nyll.AlgebraicCurves.Places.Exists_place_notMem_ord_neg_and_forall_ord_eq_one
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeInfty_X
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Models.CurveModel_exists_curveModel_iso_of_algEquiv
import Nyll.AlgebraicCurves.Models.CurveModel_exists_iso_comp_toBase_eq_placeOfPoint_congr_eq
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Nyll.SchemeTheory.Pi1.Affine.Over
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# A genus-zero curve with one puncture

A parameter with its unique pole at the prescribed puncture identifies that place with
infinity. The induced curve-model isomorphism identifies the given open complement with the
actual affine line. The fundamental group is transported through this scheme isomorphism.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale AlgebraicCurve
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

open Classical in
/-- A rational coordinate on a genus-zero function field can have its pole at any prescribed
place; the induced place equivalence sends infinity to that place. -/
theorem exists_ratFunc_algEquiv_infinity_of_genus_zero (hg : genusFF K F = 0)
    (v : Place K F) :
    ∃ e : RatFunc K ≃ₐ[K] F,
      Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
        (RationalFunctionField.placeInfty K) = v := by
  classical
  obtain ⟨w, _, hnot, _⟩ :=
    exists_place_notMem_ord_neg_and_forall_ord_eq_one (K := K) (F := F) {v}
  have hne : w ≠ v := fun h => hnot (Finset.mem_singleton.mpr h)
  obtain ⟨t, _, htr, hgen, hord⟩ := exists_parameter_of_genus_zero hg w v hne
  let e : RatFunc K ≃ₐ[K] F := (RatFunc.algEquivOfTranscendental t htr).trans
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  have heX : e RatFunc.X = t := by
    change ((RatFunc.algEquivOfTranscendental t htr) RatFunc.X : F) = t
    rw [RatFunc.algEquivOfTranscendental_X]
  refine ⟨e, ?_⟩
  let u := Place.congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
    (RationalFunctionField.placeInfty K)
  have hneg : u.ord t = -1 := by
    rw [← heX]
    exact (Place.ord_congrRingEquiv e.toRingEquiv (fun a => e.commutes a)
      (RationalFunctionField.placeInfty K) RatFunc.X).trans
        (RationalFunctionField.ord_placeInfty_X K)
  have hv : u = v := by
    by_contra huv
    rw [hord, ite_eq_right huv] at hneg
    split_ifs at hneg <;> omega
  exact hv

/-- The complement of any single closed point of a proper genus-zero curve model is isomorphic
to the affine line. Neither an affine chart nor an isomorphism is an input. -/
theorem nonempty_affineLine_iso_of_genus_zero_complement
    (M : CurveModel K F) (hg : genusFF K F = 0) (x : closedPoints M.C)
    (U : M.C.Opens) (hU : (U : Set M.C) = {x.1}ᶜ) :
    Nonempty (U.toScheme ≅ Spec (.of K[X])) := by
  classical
  obtain ⟨e, he⟩ := exists_ratFunc_algEquiv_infinity_of_genus_zero hg (M.placeOfPoint x)
  obtain ⟨N, _, _⟩ := CurveModel.exists_curveModel_iso_of_algEquiv e.symm M
  obtain ⟨i, _, hplace⟩ :=
    CurveModel.exists_iso_comp_toBase_eq_placeOfPoint_congr_eq e N M
  let z : closedPoints N.C := N.placeEquiv.symm (RationalFunctionField.placeInfty K)
  have hz : i.hom.base z.1 = x.1 := by
    have hp := hplace z
    have hzplace : N.placeOfPoint z = RationalFunctionField.placeInfty K :=
      N.placeEquiv.apply_symm_apply _
    rw [hzplace, he] at hp
    exact congrArg Subtype.val (M.placeOfPoint_bijective.1 hp)
  let V : N.C.Opens := i.hom ⁻¹ᵁ U
  have hV : (V : Set N.C) = {z.1}ᶜ := by
    apply Set.ext
    intro y
    change i.hom.base y ∈ (U : Set M.C) ↔ y ∉ {z.1}
    rw [hU, Set.mem_compl_singleton_iff, Set.mem_singleton_iff, ← hz]
    exact not_congr (Scheme.homeoOfIso i).injective.eq_iff
  obtain ⟨j⟩ := nonempty_affineLine_iso_of_complement_infinity N V hV
  exact ⟨(i.hom.preimageIso U).symm ≪≫ j⟩

/-- The actual étale fundamental group of a genus-zero curve model minus one closed point is
trivial at every geometric point in characteristic zero. -/
theorem subsingleton_fundamentalGroup_of_genus_zero_complement
    (M : CurveModel K F) (hg : genusFF K F = 0) (x : closedPoints M.C)
    (U : M.C.Opens) (hU : (U : Set M.C) = {x.1}ᶜ)
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ U.toScheme) :
    Subsingleton π₁ᵉᵗ(ξ) := by
  obtain ⟨i⟩ := nonempty_affineLine_iso_of_genus_zero_complement M hg x U hU
  have connected : ConnectedSpace U.toScheme :=
    (Scheme.homeoOfIso i).connectedSpace_iff.mpr inferInstance
  let E : FiniteEtale (Spec (.of K[X])) ≌ FiniteEtale U.toScheme :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme) ⊤ i.symm
  have pullbackEquivalence : (pullback i.hom).IsEquivalence := E.isEquivalence_functor
  let eπ : π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ ≫ i.hom) :=
    fundamentalGroupEquivOfPullbackEquivalence i.hom ξ
  have singleton : Subsingleton π₁ᵉᵗ(ξ ≫ i.hom) :=
    subsingleton_fundamentalGroup_affineLine (ξ ≫ i.hom)
  exact ⟨fun σ τ => eπ.injective (Subsingleton.elim (eπ σ) (eπ τ))⟩

end AnabelianGeometry.GeometricFundamentalGroup
