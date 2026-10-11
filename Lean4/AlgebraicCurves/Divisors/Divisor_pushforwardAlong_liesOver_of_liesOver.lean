/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Places.Place_exists_comap_algebraMap_eq_of_constantFieldExtension

/-!
# Divisor pushforward Along lies Over of lies Over
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_liesOver_of_liesOver

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace HBCAux
open _root_.AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem inertiaDegAlong_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem pushforwardAlong_apply [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F'] [DecidableEq
  (Place K F)]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (D : Divisor K F') (v : Place K F) :
    Divisor.pushforwardAlong φ hφ D v = ∑ w ∈ D.support, if w.restrictAlong φ hφ = v then D w else
      0 := by
  have h1 : ∀ w : Place K F', (w.inertiaDegAlong φ hφ : ℤ) = 1 := fun w => by
    rw [inertiaDegAlong_eq_one φ hφ w, Nat.cast_one]
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  change Divisor.pushforward F D v = _
  rw [Divisor.pushforward_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1w : (w.inertiaDeg F : ℤ) = 1 := h1 w
  by_cases hw : w.restrict F = v
  · rw [ite_eq_left hw, ite_eq_left (show w.restrictAlong φ hφ = v from hw), h1w, mul_one]
  · rw [ite_eq_right hw, ite_eq_right (show ¬ w.restrictAlong φ hφ = v from hw)]

end AlgebraicCurve.HBCAux

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver
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
    (D : AlgebraicCurve.Divisor K F') (DE : AlgebraicCurve.Divisor E F'E)
    (hover : ∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
      w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring → DE w' = D w)
    (hoff : ∀ w' : AlgebraicCurve.Place E F'E,
      (∀ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) ≠
        w.toValuationSubring) → DE w' = 0) :
    (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' =
          AlgebraicCurve.Divisor.pushforwardAlong φ hφ D v) ∧
    (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠
          v.toValuationSubring) →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' = 0) := by
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
        (AlgebraicCurve.HBCAux.mem_restrictAlong_iff φE hφE w' _).mp
          (ValuationSubring.mem_comap.mp hf)
      rw [hcomm] at h1
      have h2 : φ f ∈ w.toValuationSubring := by
        rw [← hw]
        exact ValuationSubring.mem_comap.mpr h1
      exact (AlgebraicCurve.HBCAux.mem_restrictAlong_iff φ hφ w f).mpr h2
    · intro hf
      have h2 : φ f ∈ w.toValuationSubring :=
        (AlgebraicCurve.HBCAux.mem_restrictAlong_iff φ hφ w f).mp hf
      rw [← hw] at h2
      have h1 : algebraMap F' F'E (φ f) ∈ w'.toValuationSubring :=
        ValuationSubring.mem_comap.mp h2
      rw [← hcomm] at h1
      exact ValuationSubring.mem_comap.mpr
        ((AlgebraicCurve.HBCAux.mem_restrictAlong_iff φE hφE w' _).mpr h1)
  have hunder : ∀ w' : AlgebraicCurve.Place E F'E, DE w' ≠ 0 →
      ∃ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) =
        w.toValuationSubring := by
    intro w' hne
    by_contra h
    push Not at h
    exact hne (hoff w' h)
  refine ⟨?_, ?_⟩
  · intro v' v hv
    rw [AlgebraicCurve.HBCAux.pushforwardAlong_apply,
      AlgebraicCurve.HBCAux.pushforwardAlong_apply, ← Finset.sum_filter, ← Finset.sum_filter]
    have hPv := AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE
      hfg hfgE hgen v
    have huniq_v : ∀ Q' : AlgebraicCurve.Place E FE,
        Q'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring → Q' = v' := fun Q'
          hQ' =>
      (hPv.choose_spec.2.2 Q' hQ').trans (hPv.choose_spec.2.2 v' hv).symm
    have hPw := fun w : AlgebraicCurve.Place K F' =>
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F' E F'E hfg'
        hfgE' hgen' w
    let lift : AlgebraicCurve.Place K F' → AlgebraicCurve.Place E F'E := fun w => (hPw w).choose
    have hlift : ∀ w, (lift w).toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring
      :=
      fun w => (hPw w).choose_spec.1
    have hlift_uniq : ∀ (w : AlgebraicCurve.Place K F') (Q' : AlgebraicCurve.Place E F'E),
        Q'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring → Q' = lift w :=
      fun w Q' hQ' => (hPw w).choose_spec.2.2 Q' hQ'
    symm
    refine Finset.sum_bij (fun w _ => lift w) ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw ⊢
      have hval : DE (lift w) = D w := hover _ _ (hlift w)
      refine ⟨Finsupp.mem_support_iff.mpr (by rw [hval]; exact Finsupp.mem_support_iff.mp hw.1), ?_⟩
      apply huniq_v
      rw [hsq _ _ (hlift w), hw.2]
    · intro w₁ hw₁ w₂ hw₂ h
      have h' : lift w₁ = lift w₂ := h
      apply AlgebraicCurve.Place.ext
      rw [← hlift w₁, ← hlift w₂, h']
    · intro w' hw'
      rw [Finset.mem_filter] at hw'
      have hne : DE w' ≠ 0 := Finsupp.mem_support_iff.mp hw'.1
      have hw := hunder w' hne
      let w : AlgebraicCurve.Place K F' := hw.choose
      have hww' : w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring :=
        hw.choose_spec
      refine ⟨w, ?_, (hlift_uniq w w' hww').symm⟩
      rw [Finset.mem_filter]
      refine ⟨Finsupp.mem_support_iff.mpr (by rw [← hover _ _ hww']; exact hne), ?_⟩
      apply AlgebraicCurve.Place.ext
      rw [← hsq _ _ hww', hw'.2, hv]
    · intro w hw
      exact (hover _ _ (hlift w)).symm
  · intro v' hv'
    rw [AlgebraicCurve.HBCAux.pushforwardAlong_apply]
    refine Finset.sum_eq_zero fun w' _ => ?_
    by_cases h : w'.restrictAlong φE hφE = v'
    · rw [ite_eq_left h]
      by_contra hne
      have hw := hunder w' hne
      apply hv' (hw.choose.restrictAlong φ hφ)
      rw [← h]
      exact hsq _ _ hw.choose_spec
    · rw [ite_eq_right h]
end AlgebraicCurves.Divisors.Proofs.Divisor_pushforwardAlong_liesOver_of_liesOver
end ProofImplementation
