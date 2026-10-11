/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Algebraize

/-!
# Is Local Ring mem range algebra Map of flat of is Local Hom
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom

universe u v u' v'

theorem _root_.IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain
      R] [IsDomain S]
    (f : R →+* S) (hf : f.Flat) [IsLocalHom f]
    (K : Type u') (L : Type v') [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hcomm : ∀ r : R, algebraMap R L r = algebraMap S L (f r))
    (x : K) (hx : algebraMap K L x ∈ (algebraMap S L).range) :
    x ∈ (algebraMap R K).range := by
  algebraize [f]
  have hff : Module.FaithfullyFlat R S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ inferInstance ‹_›
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨s, hs⟩ := hx
  have hKL : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (algebraMap R S r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply R K L r, hcomm r]
    rfl
  have hfb0 : algebraMap R S b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  have hdiv : algebraMap R S a = s * algebraMap R S b := by
    have h1 : algebraMap S L s =
        algebraMap S L (algebraMap R S a) / algebraMap S L (algebraMap R S b) := by
      rw [hs, map_div₀, hKL, hKL]
    have h2 : algebraMap S L (algebraMap R S b) ≠ 0 := fun h =>
      hfb0 ((IsFractionRing.to_map_eq_zero_iff (K := L)).mp h)
    apply IsFractionRing.injective S L
    rw [map_mul, h1, div_mul_cancel₀ _ h2]
  have hmem : a ∈ Ideal.comap (algebraMap R S) ((Ideal.span {b}).map (algebraMap R S)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have hbK : algebraMap R K b ≠ 0 := fun h => hb0 ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp
    h)
  rw [eq_div_iff hbK, ← map_mul, hr]

end IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
