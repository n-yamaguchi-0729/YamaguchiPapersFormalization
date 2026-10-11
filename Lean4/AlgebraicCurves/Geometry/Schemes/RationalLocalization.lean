/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ResidueField
import AlgebraicCurves.Foundations.CommutativeAlgebra.RationalLocalization

/-!
# Rational Localization
-/

open AlgebraicGeometry CategoryTheory

namespace Rat.LocalizationAt

/-- The residue-field map induced from the rational localization at a prime. -/
theorem exists_specMap_comp_eq_fromSpecResidueField
    (p : ℕ) [Fact p.Prime] (s : Spec (CommRingCat.of ℤ))
    (hs : s.asIdeal = Ideal.span {(p : ℤ)}) :
    ∃ φ : ↥(Rat.LocalizationAt p) →+* (Spec (CommRingCat.of ℤ)).residueField s,
      Function.Surjective φ ∧ φ (p : ↥(Rat.LocalizationAt p)) = 0 ∧
      Spec.map (CommRingCat.ofHom φ) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(Rat.LocalizationAt p))) =
        (Spec (CommRingCat.of ℤ)).fromSpecResidueField s := by
  have hp : p.Prime := Fact.out
  have hprime : (Ideal.span {(p : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hp
  let hsprime : s.asIdeal.IsPrime := hs ▸ hprime
  have hlocSpan : IsLocalization.AtPrime (Rat.LocalizationAt p) (Ideal.span {(p : ℤ)}) :=
    Rat.LocalizationAt.isLocalization hp
  have hM : s.asIdeal.primeCompl = (Ideal.span {(p : ℤ)}).primeCompl := by
    ext x
    change x ∈ s.asIdeal.primeCompl ↔ x ∈ (Ideal.span {(p : ℤ)}).primeCompl
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hs]
  have hloc : IsLocalization.AtPrime (Rat.LocalizationAt p) s.asIdeal := by
    change IsLocalization s.asIdeal.primeCompl (Rat.LocalizationAt p)
    rw [hM]
    exact hlocSpan
  set R : Type := ↥(Rat.LocalizationAt p)
  let L : Type := Localization.AtPrime s.asIdeal
  let K : Type := s.asIdeal.ResidueField
  let e : R ≃ₐ[ℤ] L := IsLocalization.algEquiv s.asIdeal.primeCompl R L
  let φ₀ : R →+* K := (IsLocalRing.residue L).comp e.toAlgHom.toRingHom
  let ι := Scheme.Spec.residueFieldIso (CommRingCat.of ℤ) s
  let φ : R →+* (Spec (CommRingCat.of ℤ)).residueField s := ι.inv.hom.comp φ₀
  refine ⟨φ, ?_, ?_, ?_⟩
  · apply (ι.commRingCatIsoToRingEquiv.symm.surjective).comp
    exact (IsLocalRing.residue_surjective).comp e.surjective
  · change ι.inv.hom (IsLocalRing.residue L (e (p : R))) = 0
    have he : e (p : R) = algebraMap ℤ L (p : ℤ) := by
      rw [show (p : R) = algebraMap ℤ R (p : ℤ) from
        (map_natCast (algebraMap ℤ R) p).symm, AlgEquiv.commutes]
    rw [he, (IsLocalRing.residue_eq_zero_iff _).mpr, map_zero]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff L s.asIdeal (p : ℤ)).mpr
    rw [hs]
    exact Ideal.mem_span_singleton_self _
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hcomp : φ.comp (algebraMap ℤ R) = ι.inv.hom.comp (algebraMap ℤ K) :=
      RingHom.ext_int _ _
    rw [hcomp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp]
    exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of ℤ) s

end Rat.LocalizationAt
