/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_finite_setOf_deg_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental

/-!
# Place finite set Of deg eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_finite_setOf_deg_eq

open _root_.AlgebraicCurve
open _root_.IsDedekindDomain
open _root_.Polynomial
open _root_.IntermediateField

open scoped Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace FiniteSetOfDegEqAux
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

theorem finite_setOf_natDegree_le (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {g : K[X] | g.natDegree ≤ d}.Finite := by
  have : Finite (Polynomial.degreeLT K (d + 1)) :=
    Finite.of_equiv (Fin (d + 1) → K) (Polynomial.degreeLTEquiv K (d + 1)).symm.toEquiv
  refine Set.Finite.subset (Set.toFinite (Polynomial.degreeLT K (d + 1) : Set K[X])) ?_
  intro g hg
  rw [Set.mem_ofPred_eq] at hg
  rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
  exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hg)

theorem finite_heightOneSpectrum_of_deg_eq (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {w : HeightOneSpectrum K[X] |
      (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = d}.Finite := by
  have hfin : ((fun g : K[X] => (Ideal.span {g} : Ideal K[X])) ''
      {g : K[X] | g.natDegree ≤ d}).Finite := (finite_setOf_natDegree_le K d).image _
  have hpre : ((fun w : HeightOneSpectrum K[X] => w.asIdeal) ⁻¹'
      ((fun g : K[X] => (Ideal.span {g} : Ideal K[X])) '' {g : K[X] | g.natDegree ≤ d})).Finite :=
    hfin.preimage fun w _ w' _ h => HeightOneSpectrum.ext h
  refine hpre.subset fun w hw => ?_
  obtain ⟨p, _hpirr, hwI⟩ := RationalFunctionField.exists_irreducible_span K w
  rw [Set.mem_ofPred_eq, RationalFunctionField.deg_ofHeightOneSpectrum K hwI] at hw
  exact ⟨p, le_of_eq hw, hwI.symm⟩

theorem finite_setOf_ratFunc_place_deg_eq (K : Type*) [Field K] [Finite K] (d : ℕ) :
    {v : Place K (RatFunc K) | v.deg = d}.Finite := by
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.image (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K))
        (finite_heightOneSpectrum_of_deg_eq K d))
      (Set.Subsingleton.finite
        (RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum (K := K))))
    fun v hv => ?_
  rw [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
  by_cases hcase : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum (K := K) w
  · obtain ⟨w, rfl⟩ := hcase
    exact Or.inl ⟨w, hv, rfl⟩
  · exact Or.inr fun w h => hcase ⟨w, h⟩

theorem exists_ratFunc_intermediate (K F : Type*) [Field K] [Finite K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∃ (_ : Algebra (RatFunc K) F) (_ : IsScalarTower K (RatFunc K) F)
      (_ : Algebra.IsIntegral (RatFunc K) F), Module.Finite (RatFunc K) F := by
  have : PerfectField K := inferInstance
  obtain ⟨t, htr, hfd, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t htr
  let iAlgF : Algebra (RatFunc K) F := ((K⟮t⟯.val).comp e.toAlgHom).toRingHom.toAlgebra
  let iAlgKt : Algebra (RatFunc K) K⟮t⟯ := e.toAlgHom.toRingHom.toAlgebra
  have iSTF : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => (((K⟮t⟯.val).comp e.toAlgHom).commutes a).symm
  have iSTtF : IsScalarTower (RatFunc K) K⟮t⟯ F :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have iFinKt : Module.Finite (RatFunc K) K⟮t⟯ :=
    ⟨⟨{1}, by
      rw [Finset.coe_singleton, Submodule.span_singleton_eq_top_iff]
      exact fun x => ⟨e.symm x, by
        change algebraMap (RatFunc K) K⟮t⟯ (e.symm x) * 1 = x
        rw [mul_one]; exact e.apply_symm_apply x⟩⟩⟩
  have iFinF : Module.Finite (RatFunc K) F := Module.Finite.trans K⟮t⟯ F
  have iIntF : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  exact ⟨iAlgF, iSTF, iIntF, iFinF⟩

end AlgebraicCurve.Place.FiniteSetOfDegEqAux

open AlgebraicCurve.Place.FiniteSetOfDegEqAux in
theorem _root_.AlgebraicCurve.Place.finite_setOf_deg_eq
    (K F : Type*) [Field K] [Finite K] [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F] (d : ℕ) :
    {v : Place K F | v.deg = d}.Finite := by
  obtain ⟨iAlg, iST, iInt, iFin⟩ := exists_ratFunc_intermediate K F
  have hsub : {w : Place K F | w.deg = d}
      ⊆ ⋃ v ∈ (⋃ d' ∈ Finset.range (d + 1), {v : Place K (RatFunc K) | v.deg = d'}),
          {w : Place K F | w.restrict (RatFunc K) = v} := by
    intro w hw
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, exists_prop]
    refine ⟨w.restrict (RatFunc K), ⟨(w.restrict (RatFunc K)).deg, ?_, rfl⟩, rfl⟩
    have htow := w.deg_restrict_mul_inertiaDeg (F := RatFunc K)
    have : Module.Finite K w.ResidueField := IsCurveOver.finite_residueField w
    have hdpos : 0 < w.deg := by
      change 0 < Module.finrank K w.ResidueField
      exact Module.finrank_pos
    rw [Set.mem_ofPred_eq] at hw
    have hine : 0 < w.inertiaDeg (RatFunc K) := by
      rcases Nat.eq_zero_or_pos (w.inertiaDeg (RatFunc K)) with h0 | hp
      · exfalso; rw [h0, Nat.mul_zero] at htow; omega
      · exact hp
    calc (w.restrict (RatFunc K)).deg
        ≤ (w.restrict (RatFunc K)).deg * w.inertiaDeg (RatFunc K) :=
          Nat.le_mul_of_pos_right _ hine
      _ = d := htow.trans hw
      _ < d + 1 := Nat.lt_succ_self d
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion ?_ fun v _ => Place.restrict_fiber_finite v
  exact Set.Finite.biUnion (Finset.range (d + 1)).finite_toSet
    fun d' _ => finite_setOf_ratFunc_place_deg_eq K d'
end AlgebraicCurves.Places.Proofs.Place_finite_setOf_deg_eq
end ProofImplementation

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
