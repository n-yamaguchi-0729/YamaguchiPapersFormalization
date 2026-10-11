/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_liesOver_of_liesOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import AlgebraicCurves.Places.Place_exists_toValuationSubring_eq_comap_ringHom

/-!
# Divisor pullback Along lies Over of lies Over
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_liesOver_of_liesOver

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace A1Aux
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem restrictAlong_toValuationSubring (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom :=
  rfl

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

end AlgebraicCurve.A1Aux

theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_liesOver_of_liesOver
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
      [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F'
      F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} :
      Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} :
      Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} :
      Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [AlgebraicCurve.IsCurveOver
      E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (φE : FE →ₐ[E] F'E) (hφE :
      φE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (D : AlgebraicCurve.Divisor K F) (DE : AlgebraicCurve.Divisor E FE)
    (hover : ∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
      v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring → DE v' = D v)
    (hoff : ∀ v' : AlgebraicCurve.Place E FE,
      (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠
        v.toValuationSubring) → DE v' = 0) :
    (∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
        w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring →
        AlgebraicCurve.Divisor.pullbackAlong φE hφE DE w' = AlgebraicCurve.Divisor.pullbackAlong φ
          hφ D w) ∧
    (∀ w' : AlgebraicCurve.Place E F'E,
        (∀ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) ≠
          w.toValuationSubring) →
        AlgebraicCurve.Divisor.pullbackAlong φE hφE DE w' = 0) := by
  classical
  have hsq : ∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
      w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring →
      (w'.restrictAlong φE hφE).toValuationSubring.comap (algebraMap F FE)
        = (w.restrictAlong φ hφ).toValuationSubring := by
    intro w' w hw
    ext f
    constructor
    · intro hf
      have h1 : φE (algebraMap F FE f) ∈ w'.toValuationSubring :=
        (AlgebraicCurve.A1Aux.mem_restrictAlong_iff φE hφE w' _).mp (ValuationSubring.mem_comap.mp
          hf)
      rw [hcomm] at h1
      have h2 : φ f ∈ w.toValuationSubring := by
        rw [← hw]
        exact ValuationSubring.mem_comap.mpr h1
      exact (AlgebraicCurve.A1Aux.mem_restrictAlong_iff φ hφ w f).mpr h2
    · intro hf
      have h2 : φ f ∈ w.toValuationSubring :=
        (AlgebraicCurve.A1Aux.mem_restrictAlong_iff φ hφ w f).mp hf
      rw [← hw] at h2
      have h1 : algebraMap F' F'E (φ f) ∈ w'.toValuationSubring :=
        ValuationSubring.mem_comap.mp h2
      rw [← hcomm] at h1
      exact ValuationSubring.mem_comap.mpr
        ((AlgebraicCurve.A1Aux.mem_restrictAlong_iff φE hφE w' _).mpr h1)
  refine ⟨?_, ?_⟩
  · intro w' w hw
    rw [AlgebraicCurve.Divisor.pullbackAlong_apply, AlgebraicCurve.Divisor.pullbackAlong_apply,
      hover _ _ (hsq w' w hw)]
    have h1 := AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F E FE hfg hfgE hgen (w.restrictAlong φ hφ)
    obtain ⟨P', -, hP'ord, hP'uniq⟩ := h1
    have hv'P : w'.restrictAlong φE hφE = P' := hP'uniq _ (hsq w' w hw)
    have h2 := AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F' E F'E hfg' hfgE' hgen' w
    obtain ⟨Q', -, hQ'ord, hQ'uniq⟩ := h2
    have hw'Q : w' = Q' := hQ'uniq _ hw
    obtain ⟨π, hπ⟩ :=
      IsDiscreteValuationRing.exists_irreducible (w.restrictAlong φ hφ).toValuationSubring
    have hπ1 : (w.restrictAlong φ hφ).ord (π : F) = 1 :=
      (w.restrictAlong φ hφ).ord_coe_irreducible hπ
    have hπ1' : (w'.restrictAlong φE hφE).ord (algebraMap F FE (π : F)) = 1 := by
      rw [hv'P, hP'ord, hπ1]
    have hE : (AlgebraicCurve.Place.ramificationIndexAlong φE w' : ℤ)
        = AlgebraicCurve.Place.ramificationIndexAlong φ w := by
      calc (AlgebraicCurve.Place.ramificationIndexAlong φE w' : ℤ)
          = AlgebraicCurve.Place.ramificationIndexAlong φE w'
              * (w'.restrictAlong φE hφE).ord (algebraMap F FE (π : F)) := by
            rw [hπ1', mul_one]
        _ = w'.ord (φE (algebraMap F FE (π : F))) :=
            (AlgebraicCurve.Place.ord_restrictAlong φE hφE w' _).symm
        _ = w'.ord (algebraMap F' F'E (φ (π : F))) := by rw [hcomm]
        _ = w.ord (φ (π : F)) := by rw [hw'Q]; exact hQ'ord _
        _ = AlgebraicCurve.Place.ramificationIndexAlong φ w * (w.restrictAlong φ hφ).ord (π : F) :=
            AlgebraicCurve.Place.ord_restrictAlong φ hφ w _
        _ = AlgebraicCurve.Place.ramificationIndexAlong φ w := by rw [hπ1, mul_one]
    rw [hE]
  · intro w' hw'
    rw [AlgebraicCurve.Divisor.pullbackAlong_apply]
    suffices h0 : DE (w'.restrictAlong φE hφE) = 0 by rw [h0, mul_zero]
    apply hoff
    intro v hveq
    obtain ⟨g, hg⟩ : ∃ g : F, g ∉ v.toValuationSubring := by
      by_contra h
      push Not at h
      exact v.ne_top' (SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => h x⟩)
    have hg' : algebraMap F' F'E (φ g) ∉ w'.toValuationSubring := by
      intro hmem
      apply hg
      rw [← hveq]
      refine ValuationSubring.mem_comap.mpr
        ((AlgebraicCurve.A1Aux.mem_restrictAlong_iff φE hφE w' _).mpr ?_)
      rw [hcomm]
      exact hmem
    obtain ⟨x, -, hxfin⟩ := hfg'
    have := hxfin
    have hwK : ∀ a : K, algebraMap F' F'E (algebraMap K F' a) ∈ w'.toValuationSubring := by
      intro a
      rw [← IsScalarTower.algebraMap_apply K F' F'E, IsScalarTower.algebraMap_apply K E F'E]
      exact w'.algebraMap_mem' _
    obtain ⟨u, hu⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
      (K := K) x (algebraMap F' F'E) w'.toValuationSubring hwK ⟨φ g, hg'⟩
    exact hw' u hu.symm
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_liesOver_of_liesOver
end ProofImplementation
