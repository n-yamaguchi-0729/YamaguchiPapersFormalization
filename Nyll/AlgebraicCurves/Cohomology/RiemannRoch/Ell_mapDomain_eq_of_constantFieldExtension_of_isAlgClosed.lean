/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.FunctionFields.LinearIndependent_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.FunctionFields.Mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Nyll.AlgebraicCurves.FunctionFields.Exists_separating_transcendental_of_perfectField
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed

/-!
# Ell map Domain eq of constant Field Extension of is Alg Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EllMapDomainConstantsAlgClosed
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

namespace W7XEllMapDomain

variable {K F K' F' : Type*}
  [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
  [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']

omit [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F'] in
theorem algebraMap_mem_of_new
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {v' : Place K' F'}
    (hv' : ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (f : F) : algebraMap F F' f ∈ v'.toValuationSubring := by
  by_contra hmem
  obtain ⟨x, hxt, hxfin⟩ := hfg
  obtain ⟨t, _ht_trans, ht_fin, ht_sep⟩ :=
    AlgebraicCurve.exists_separating_transcendental_of_perfectField hxt hxfin
  have := ht_fin; have := ht_sep
  obtain ⟨P, hP⟩ :=
    AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
      (K := K) t (algebraMap F F') v'.toValuationSubring
      (fun c => by
        rw [← IsScalarTower.algebraMap_apply K F F', IsScalarTower.algebraMap_apply K K' F']
        exact v'.algebraMap_mem' _)
      ⟨f, hmem⟩
  exact hv' P hP.symm

omit [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F'] in
theorem algebraMap_mem_lSpace
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {lift : Place K F → Place K' F'}
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    {D : Divisor K F} {f : F} (hf : f ∈ LSpace D) :
    algebraMap F F' f ∈ LSpace (K := K') (Finsupp.mapDomain lift D) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v' => ?_)
  by_cases hold : ∃ v, lift v = v'
  · obtain ⟨v, rfl⟩ := hold
    rw [Finsupp.mapDomain_apply_of_injective hlift_inj, hlift_ord]
    exact (mem_lSpace_iff_ord.mp hf).resolve_left hf0 v
  · push Not at hold
    rw [show (Finsupp.mapDomain lift D) v' = 0 from
      Finsupp.mapDomain_of_notMem_range D v' (by simpa [Set.range] using hold), neg_zero]
    have hmem := algebraMap_mem_of_new (K' := K') (F' := F') hfg (hlift_new v' hold) f
    rcases (v'.adicValuation_le_one_iff).mp (v'.adicValuation_le_one_of_mem hmem) with h0 | h
    · exact absurd ((algebraMap F F').injective (h0.trans (map_zero _).symm)) hf0
    · exact h

end W7XEllMapDomain

open W7XEllMapDomain

theorem _root_.AlgebraicCurve.ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (D : Divisor K F) [FiniteDimensional K ↥(riemannRochSpace D)] :
    ell (K := K') (D.mapDomain lift) = ell (K := K) D := by
  classical
  set b := Module.finBasis K ↥(riemannRochSpace D) with hb
  set n := ell (K := K) D with hn
  set e : Fin n → ↥(LSpace (K := K') (Finsupp.mapDomain lift D)) :=
    fun i => ⟨algebraMap F F' (b i).1,
      algebraMap_mem_lSpace hfg hlift_ord hlift_inj hlift_new (b i).2⟩ with he
  have hLI : LinearIndependent K' e := by
    have hLI0 : LinearIndependent K' (fun i => algebraMap F F' (b i : F)) :=
      linearIndependent_of_constantFieldExtension_of_isAlgClosed K F K' F' hfg hfg' hgen
        (b.linearIndependent.map' (riemannRochSpace D).subtype
          (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
    exact hLI0.of_comp (LSpace (K := K') (Finsupp.mapDomain lift D)).subtype
  have hSpan : Submodule.span K' (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨f', hf'⟩ -
    have hmem_img : f' ∈ Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) :=
      lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
        K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj hlift_new D hf'
    have heq : Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) D : Set F)) =
        Submodule.span K' (Set.range fun i => algebraMap F F' (b i : F)) := by
      refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨g, hg, rfl⟩
        have : algebraMap F F' g = ∑ i, (algebraMap K K' (b.repr ⟨g, hg⟩ i)) •
            algebraMap F F' (b i : F) := by
          conv_lhs => rw [show g = ((⟨g, hg⟩ : riemannRochSpace D) : F) from rfl,
            ← b.sum_repr ⟨g, hg⟩]
          simp only [Submodule.coe_sum, SetLike.val_smul, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K F F',
            Algebra.smul_def, IsScalarTower.algebraMap_apply K K' F']
        rw [this]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · rintro _ ⟨i, rfl⟩; exact ⟨_, (b i).2, rfl⟩
    rw [heq] at hmem_img
    have hmap : Submodule.span K' (Set.range fun i => algebraMap F F' (b i : F)) =
        (Submodule.span K' (Set.range e)).map
          (LSpace (K := K') (Finsupp.mapDomain lift D)).subtype := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hmem_img
    obtain ⟨y, hy, hyf⟩ := hmem_img
    rwa [show y = ⟨f', hf'⟩ from Subtype.ext hyf] at hy
  have hBasis : Module.Basis (Fin n) K' ↥(LSpace (K := K') (Finsupp.mapDomain lift D)) :=
    .mk hLI (le_of_eq hSpan.symm)
  calc ell (K := K') (D.mapDomain lift)
      = Fintype.card (Fin n) := Module.finrank_eq_card_basis hBasis
    _ = n := Fintype.card_fin n
    _ = ell (K := K) D := hn
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.EllMapDomainConstantsAlgClosed
end ProofImplementation
