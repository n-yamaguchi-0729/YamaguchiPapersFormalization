/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isCurveOver_and_essFiniteType_of_le_of_transcendental_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_perfectField

/-!
# Is Curve Over and ess Finite Type of le of transcendental mem
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace IsCurveOver_and_essFiniteType_of_le_of_transcendental_mem
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

namespace IsCurveOfSubfield

open IntermediateField

variable {K F : Type} [Field K] [Field F] [Algebra K F]

section Exchange

theorem finiteDimensional_adjoin_of_transcendental {x₀ : F} (hx₀ : Transcendental K x₀)
    (hfd : FiniteDimensional K⟮x₀⟯ F) {t : F} (ht : Transcendental K t) : FiniteDimensional K⟮t⟯ F
      := by
  have halg₀ : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun _ : Fin 1 => x₀)) F := by
    have : Algebra.IsAlgebraic K⟮x₀⟯ F := Algebra.IsAlgebraic.of_finite _ _
    rw [Set.range_const]
    exact IntermediateField.isAlgebraic_adjoin_iff_top.mp this
  have hb₀ : IsTranscendenceBasis K (fun _ : Fin 1 => x₀) :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨(algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hx₀, halg₀⟩
  have htr : Algebra.trdeg K F = Cardinal.mk (Fin 1) := hb₀.cardinalMk_eq_trdeg.symm
  have hbt : IsTranscendenceBasis K (fun _ : Fin 1 => t) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (0 : Fin 1)).mpr ht) htr.le
  have halg : Algebra.IsAlgebraic K⟮t⟯ F := by
    have h := hbt.isAlgebraic_field
    rwa [Set.range_const] at h
  set L := K⟮t⟯
  have hint : IsIntegral L x₀ := (halg.isAlgebraic x₀).isIntegral
  set N : IntermediateField L F := L⟮x₀⟯
  have : FiniteDimensional L N := IntermediateField.adjoin.finiteDimensional hint
  have hmem : ∀ s : K⟮x₀⟯, (s : F) ∈ N := by
    intro s
    have hle : K⟮x₀⟯ ≤ N.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self L x₀)
    exact hle s.2
  let : Algebra K⟮x₀⟯ N := RingHom.toAlgebra
    { toFun := fun s => ⟨(s : F), hmem s⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : IsScalarTower K⟮x₀⟯ N F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite N F := Module.Finite.of_restrictScalars_finite K⟮x₀⟯ N F
  exact Module.Finite.trans N F

end Exchange

section Transport

variable {E : Type} [Field E] [Algebra K E] (j : E →ₐ[K] F) (hj : Function.Injective j) (x : E)

theorem map_adjoin_x : IntermediateField.map j (IntermediateField.adjoin K ({x} : Set E)) =
    IntermediateField.adjoin K ({j x} : Set F) := by
  rw [IntermediateField.adjoin_map, Set.image_singleton]

/-- The equivalence between the simple intermediate fields generated before and after the
embedding. -/
noncomputable def e : (IntermediateField.adjoin K ({x} : Set E)) ≃ₐ[K] (IntermediateField.adjoin K
  ({j x} : Set F)) :=
  (IntermediateField.equivMap _ j).trans (IntermediateField.equivOfEq (map_adjoin_x j x))

theorem coe_e (l : IntermediateField.adjoin K ({x} : Set E)) :
    ((e j x l : IntermediateField.adjoin K ({j x} : Set F)) : F) = j (l : E) := by
  simp [e, IntermediateField.equivMap]
  rfl
include hj in
theorem finiteDimensional_E (hfd : FiniteDimensional (IntermediateField.adjoin K ({j x} : Set F))
  F) :
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set E)) E := by
  set L' := IntermediateField.adjoin K ({x} : Set E)
  set L := IntermediateField.adjoin K ({j x} : Set F)
  let : Algebra E F := j.toRingHom.toAlgebra
  let : Algebra L' F := ((algebraMap E F).comp (algebraMap L' E)).toAlgebra
  have : IsScalarTower L' E F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite L' F := by
    refine Module.Finite.of_equiv_equiv (A₁ := L) (B₁ := F) (e j x).symm.toRingEquiv
      (RingEquiv.refl F) ?_
    ext l
    change algebraMap L' F ((e j x).symm l) = (l : F)
    change j ((((e j x).symm l : L') : E)) = (l : F)
    rw [← coe_e j x ((e j x).symm l), AlgEquiv.apply_symm_apply]
  let ι : E →ₗ[L'] F :=
    { toFun := fun v => j v
      map_add' := fun _ _ => map_add j _ _
      map_smul' := fun c v => by
        change j ((c : E) * v) = algebraMap L' F c * j v
        rw [map_mul]
        rfl }
  exact Module.Finite.of_injective ι hj

end Transport

section EssFT

theorem essFiniteType_of_adjoin_finset {K E : Type} [Field K] [Field E] [Algebra K E]
    (S : Finset E) (hS : IntermediateField.adjoin K (S : Set E) = ⊤) : Algebra.EssFiniteType K E :=
      by
  set A : Subalgebra K E := Algebra.adjoin K (S : Set E) with hA
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset
    S)
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  have : IsFractionRing A E := by
    apply IsFractionRing.of_field
    intro z
    have hz : z ∈ IntermediateField.adjoin K (S : Set E) := by rw [hS]; trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  have : Algebra.EssFiniteType K A := Algebra.EssFiniteType.of_finiteType K A
  have : Algebra.EssFiniteType A E := Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp K A E

theorem exists_finset_adjoin_eq_top {K E : Type} [Field K] [Field E] [Algebra K E] (x : E)
    [hfd : FiniteDimensional K⟮x⟯ E] : ∃ S : Finset E, IntermediateField.adjoin K (S : Set E) = ⊤
      := by
  classical
  set L := K⟮x⟯
  let b := Module.finBasis L E
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  rw [eq_top_iff]
  intro v _
  set T : IntermediateField K E := IntermediateField.adjoin K ((insert x (Finset.univ.image b) :
    Finset E) : Set E)
  have hL : L ≤ T := IntermediateField.adjoin.mono K _ _ (by
    intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact_mod_cast Finset.mem_insert_self x _)
  have hb : ∀ i, b i ∈ T := fun i =>
    IntermediateField.subset_adjoin K _
      (by exact_mod_cast Finset.mem_insert_of_mem (Finset.mem_image_of_mem b (Finset.mem_univ i)))
  rw [← b.sum_repr v]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hL (b.repr v i).2) (hb i)

end EssFT

end IsCurveOfSubfield

open IsCurveOfSubfield in
theorem _root_.AlgebraicCurve.isCurveOver_and_essFiniteType_of_le_of_transcendental_mem
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed K]
    (E F : IntermediateField K Ω) (hEF : E ≤ F) (t : Ω) (htE : t ∈ E) (ht : Transcendental K t)
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F) :
    AlgebraicCurve.IsCurveOver K E ∧ Algebra.EssFiniteType K E ∧
      (∃ y : E, Transcendental K y ∧ FiniteDimensional (IntermediateField.adjoin K ({y} : Set E))
        E) := by
  obtain ⟨x₀, hx₀, hfd₀⟩ := hfg
  set tE : E := ⟨t, htE⟩
  set tF : F := ⟨t, hEF htE⟩
  have htF : Transcendental K tF :=
    (transcendental_algebraMap_iff (R := K) (S := F) (A := Ω) Subtype.val_injective).mp ht
  have htE' : Transcendental K tE :=
    (transcendental_algebraMap_iff (R := K) (S := E) (A := Ω) Subtype.val_injective).mp ht
  have hfd : FiniteDimensional (IntermediateField.adjoin K ({tF} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental hx₀ hfd₀ htF
  set j : E →ₐ[K] F := IntermediateField.inclusion hEF
  have hj : Function.Injective j := fun a b h => Subtype.ext (congrArg Subtype.val h : ((j a : F) :
    Ω) = (j b : F))
  have hjt : j tE = tF := rfl
  have hfdE : FiniteDimensional (IntermediateField.adjoin K ({tE} : Set E)) E := by
    have h := finiteDimensional_E j hj tE
    rw [hjt] at h
    exact h hfd
  have := hfdE
  obtain ⟨S, hS⟩ := exists_finset_adjoin_eq_top (K := K) (E := E) tE
  exact ⟨AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htE' hfdE,
    essFiniteType_of_adjoin_finset S hS, tE, htE', hfdE⟩
end AlgebraicCurves.FunctionFields.Proofs.IsCurveOver_and_essFiniteType_of_le_of_transcendental_mem
end ProofImplementation
