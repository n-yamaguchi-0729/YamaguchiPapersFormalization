/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_sub_algebraMap_pos_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Place_mem_iff_ord_nonneg
import Nyll.AlgebraicCurves.Places.Place_exists_of_valuationSubring_of_isSeparable

/-!
# Place exists ord sub algebra Map pos of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_ord_sub_algebraMap_pos_of_transcendental

open AlgebraicCurve
open scoped IntermediateField

namespace POV

theorem transcendental_sub_algebraMap {K M : Type*} [Field K] [Field M] [Algebra K M] {t : M} (ht :
  Transcendental K t) (c : K) :
    Transcendental K (t - algebraMap K M c) := by
  intro halg
  apply ht
  have : t = (t - algebraMap K M c) + algebraMap K M c := by ring
  rw [this]
  exact halg.add (isAlgebraic_algebraMap c)

theorem not_isUnit_of_transcendental {K M : Type*} [Field K] [Field M] [Algebra K M] {f : M} (hf :
  Transcendental K f) :
    ¬ IsUnit (⟨f, Algebra.subset_adjoin (Set.mem_singleton f)⟩ : Algebra.adjoin K ({f} : Set M)) :=
      by
  intro hu
  obtain ⟨g, hg⟩ := hu.exists_right_inv
  have hgmem : (g : M) ∈ (Polynomial.aeval (R := K) f).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval K f]; exact g.2
  obtain ⟨q, hq⟩ := hgmem
  have hinj : Function.Injective (Polynomial.aeval (R := K) f) := transcendental_iff_injective.mp hf
  have h1 : Polynomial.aeval (R := K) f (Polynomial.X * q) = Polynomial.aeval (R := K) f 1 := by
    rw [map_mul, Polynomial.aeval_X, map_one, show Polynomial.aeval f q = (g : M) from hq]
    exact congrArg Subtype.val hg
  have h2 : (Polynomial.X * q : Polynomial K) = 1 := hinj h1
  have h3 : IsUnit (Polynomial.X : Polynomial K) := IsUnit.of_mul_eq_one _ h2
  exact Polynomial.not_isUnit_X h3

end POV

open POV in
theorem _root_.AlgebraicCurve.Place.exists_ord_sub_algebraMap_pos_of_transcendental {K M : Type*}
  [Field K] [Field M] [Algebra K M] (t : M) (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ M] [Algebra.IsSeparable K⟮t⟯ M] (c : K) :
    ∃ v : AlgebraicCurve.Place K M, 0 < v.ord (t - algebraMap K M c) := by
  classical
  set f : M := t - algebraMap K M c with hfdef
  have hf : Transcendental K f := transcendental_sub_algebraMap ht c
  have hf0 : f ≠ 0 := fun h => hf (by rw [h]; exact isAlgebraic_zero)
  let R : Subring M := (Algebra.adjoin K ({f} : Set M)).toSubring
  let fR : R := ⟨f, Algebra.subset_adjoin (Set.mem_singleton f)⟩
  have hfR : ¬ IsUnit fR := not_isUnit_of_transcendental hf
  obtain ⟨𝔭, h𝔭max, hf𝔭⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hfR)
  have : 𝔭.IsPrime := h𝔭max.isPrime
  let L : LocalSubring M := LocalSubring.ofPrime R 𝔭
  obtain ⟨B, hB⟩ := L.exists_le_valuationSubring
  obtain ⟨hLB, hloc⟩ := LocalSubring.le_def.mp hB
  have hfL : ¬ IsUnit (algebraMap R L.toSubring fR) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff L.toSubring 𝔭 fR]
    exact fun h => h hf𝔭
  have hfLval : ((algebraMap R L.toSubring fR : L.toSubring) : M) = f := rfl
  have hfB_mem : f ∈ B := by
    have : ((algebraMap R L.toSubring fR : L.toSubring) : M) ∈ B.toSubring := hLB (algebraMap R
      L.toSubring fR).2
    exact this
  have hfB : ¬ IsUnit (⟨f, hfB_mem⟩ : B) := by
    intro hu
    apply hfL
    have hincl : Subring.inclusion hLB (algebraMap R L.toSubring fR) = ⟨f, hfB_mem⟩ := Subtype.ext
      hfLval
    have := hloc
    exact (isUnit_map_iff (Subring.inclusion hLB) _).mp (hincl ▸ hu)
  have hBK : ∀ a : K, algebraMap K M a ∈ B := by
    intro a
    have haR : algebraMap K M a ∈ R := (Algebra.adjoin K ({f} : Set M)).algebraMap_mem a
    have : ((algebraMap R L.toSubring ⟨_, haR⟩ : L.toSubring) : M) ∈ B.toSubring := hLB (algebraMap
      R L.toSubring ⟨_, haR⟩).2
    exact this
  have hBtop : B ≠ ⊤ := by
    intro htop
    apply hfB
    have : IsUnit f := isUnit_iff_ne_zero.mpr hf0
    refine ⟨⟨⟨f, hfB_mem⟩, ⟨f⁻¹, by rw [htop]; trivial⟩,
      Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext (inv_mul_cancel₀ hf0)⟩, rfl⟩
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_isSeparable t B hBK hBtop
  refine ⟨v, ?_⟩
  have hfv : f ∈ v.toValuationSubring := hv ▸ hfB_mem
  have h0 : 0 ≤ v.ord f := (v.mem_iff_ord_nonneg hf0).mp hfv
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hinv : f⁻¹ ∈ v.toValuationSubring := by
      rw [v.mem_iff_ord_nonneg (inv_ne_zero hf0), v.ord_inv, ← h, neg_zero]
    apply hfB
    have hinvB : f⁻¹ ∈ B := hv ▸ hinv
    exact ⟨⟨⟨f, hfB_mem⟩, ⟨f⁻¹, hinvB⟩, Subtype.ext (mul_inv_cancel₀ hf0), Subtype.ext
      (inv_mul_cancel₀ hf0)⟩, rfl⟩
end AlgebraicCurves.Places.Proofs.Place_exists_ord_sub_algebraMap_pos_of_transcendental
end ProofImplementation
