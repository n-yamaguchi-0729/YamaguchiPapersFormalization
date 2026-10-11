/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Differentials.Trace
import AlgebraicCurves.Differentials.TraceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
import AlgebraicCurves.Differentials.TraceDiff_apply

/-!
# Divisor correspondence eq ord norm and dlog norm eq trace Along pullback Along
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace DlogCorrespondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mul_pullbackAlong_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {n : ℤ} {D : Divisor K F} {f : F}
    (hD : ∀ v : Place K F, n * D v = v.ord f) (w : Place K F') :
    n * Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  rw [Divisor.pullbackAlong_apply, mul_left_comm, hD, Place.ord_restrictAlong φ hφ]

theorem mul_pushforwardAlong_eq_ord (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) {n : ℤ} {E : Divisor K F'} {g : F'}
    (hg : g ≠ 0) (hE : ∀ w : Place K F', n * E w = w.ord g) (v : Place K F) :
    n * Divisor.pushforwardAlong ψ hψ E v =
      v.ord (letI := algebraAlong ψ; Algebra.norm F g) := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have := isIntegral_along ψ hψ
  have : Module.Finite F F' := hfin
  have hE' : ∀ w : Place K F', (n • E) w = w.ord g := fun w => by
    rw [Finsupp.smul_apply, smul_eq_mul, hE w]
  have h := hN g hg (n • E) hE' v
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
  exact h

theorem norm_along_ne_zero (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) {g : F'} (hg : g ≠ 0) :
    (letI := algebraAlong ψ; Algebra.norm F g) ≠ 0 := by
  let := algebraAlong ψ
  have : Module.Finite F F' := hfin
  exact Algebra.norm_ne_zero_iff.mpr hg

theorem mul_correspondence_eq_ord [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) {n : ℤ} {D : Divisor K F} {f : F}
    (hf : f ≠ 0) (hD : ∀ v : Place K F, n * D v = v.ord f) (v : Place K F) :
    n * Divisor.correspondence φ ψ hφ hψ D v =
      v.ord (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [Divisor.correspondence_apply]
  exact mul_pushforwardAlong_eq_ord ψ hψ hfin hN ((map_ne_zero φ).mpr hf)
    (mul_pullbackAlong_eq_ord φ hφ hD) v

theorem pullbackAlong_dlog (φ : F →ₐ[K] F') (f : F) :
    Differential.pullbackAlong φ (f⁻¹ • D K F f) = (φ f)⁻¹ • D K F' (φ f) := by
  rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, map_inv₀]

theorem traceAlong_apply_eq_traceDiff (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ)
    (ω' : Ω[F'⁄K]) :
    Differential.traceAlong ψ ω' =
      (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; traceDiff K F F' ω') := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have : Algebra.IsSeparable F F' := hsep
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
      have htm : tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω) =
          u • Differential.pullbackAlong ψ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong ψ hsep]
      exact (AlgebraicCurve.traceDiff_apply K F F' u ω).symm

theorem traceAlong_dlog (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (g : F') :
    Differential.traceAlong ψ (g⁻¹ • D K F' g) =
      (letI := algebraAlong ψ; Algebra.norm F g)⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F g) := by
  let := algebraAlong ψ
  have := isScalarTower_along ψ
  have : Algebra.IsSeparable F F' := hsep
  rw [traceAlong_apply_eq_traceDiff ψ hsep]
  exact AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm K F F' g

theorem traceAlong_pullbackAlong_dlog (φ ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (f : F) :
    Differential.traceAlong ψ (Differential.pullbackAlong φ (f⁻¹ • D K F f)) =
      (letI := algebraAlong ψ; Algebra.norm F (φ f))⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [pullbackAlong_dlog, traceAlong_dlog ψ hsep]

theorem differentialCorrespondence_dlog (φ ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (f : F) :
    Differential.correspondence ψ φ (f⁻¹ • D K F f) =
      (letI := algebraAlong ψ; Algebra.norm F (φ f))⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [Differential.correspondence_apply, traceAlong_pullbackAlong_dlog φ ψ hsep]

theorem correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ)
    (n : ℤ) (D : Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : Place K F, n * Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        Differential.traceAlong ψ
          (Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) :=
  ⟨(letI := algebraAlong ψ; Algebra.norm F (φ f)), rfl,
    norm_along_ne_zero ψ hfin ((map_ne_zero φ).mpr hf),
    mul_correspondence_eq_ord φ ψ hφ hψ hfin hN hf hD,
    (traceAlong_pullbackAlong_dlog φ ψ hsep f).symm⟩

theorem exists_rep_of_mem_torsion {p : ℕ} {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F), Pic0.mk D = x ∧ f ≠ 0 ∧
      ∀ v : Place K F, (p : ℤ) * (D : Divisor K F) v = v.ord f := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.mem_torsion] at hx
  have hmk : (Pic0.mk ((p : ℤ) • D) : Pic0 K F) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.mk_zsmul]; exact hx
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hmk
  obtain ⟨f, hf, hDf⟩ := hmk
  refine ⟨D, f, rfl, hf, fun v => ?_⟩
  rw [← hDf v]
  rfl

theorem dlogMap_correspondence [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0 K F → Ω[F⁄K])
    (hδ : ∀ (x : Pic0 K F) (E : Divisor.degZero (K := K) (F := F)) (g : F), Pic0.mk E = x →
      g ≠ 0 → (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    δ (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
      Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by
  obtain ⟨D, f, rfl, hf, hD⟩ := exists_rep_of_mem_torsion hx
  obtain ⟨g, -, hg0, hg, hdlog⟩ :=
    correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong φ ψ hφ hψ hfin hN hsep
      (p : ℤ) (D : Divisor K F) f hf hD
  rw [hδ (Pic0.mk D) D f rfl hf hD, ← hdlog, Pic0.correspondence_mk]
  exact hδ _ (Pic0.degZeroCorrespondence φ ψ hφ hψ hFI D) g rfl hg0 hg

theorem dlogMap_correspondence' [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0 K F → Ω[F⁄K])
    (hδ : ∀ (x : Pic0 K F) (E : Divisor.degZero (K := K) (F := F)) (g : F), Pic0.mk E = x →
      g ≠ 0 → (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    δ (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) = Differential.correspondence ψ φ (δ x) := by
  rw [Differential.correspondence_apply]
  exact dlogMap_correspondence φ ψ hφ hψ hFI hfin hN hsep p δ hδ hx

theorem correspondence_mem_torsion [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (p : ℕ) {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN x ∈ Pic0.torsion K F p := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← map_zsmul, hx, map_zero]

theorem dlogMap_torsion_correspondence [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0.torsion K F p → Ω[F⁄K])
    (hδ : ∀ (x : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
      Pic0.mk E = (x : Pic0 K F) → g ≠ 0 →
      (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    (x y : Pic0.torsion K F p)
    (hxy : (y : Pic0 K F) = Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) :
    δ y = Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by
  obtain ⟨D, f, hDx, hf, hD⟩ := exists_rep_of_mem_torsion x.2
  obtain ⟨g, -, hg0, hg, hdlog⟩ :=
    correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong φ ψ hφ hψ hfin hN hsep
      (p : ℤ) (D : Divisor K F) f hf hD
  rw [hδ x D f hDx hf hD, ← hdlog]
  refine hδ y (Pic0.degZeroCorrespondence φ ψ hφ hψ hFI D) g ?_ hg0 hg
  rw [hxy, ← hDx, Pic0.correspondence_mk]

end DlogCorrespondence

end AlgebraicCurve

end

open AlgebraicCurve.DlogCorrespondence
  renaming correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong →
    correspondenceNormTraceProof in
theorem
  _root_.AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K ψ) (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hsep : AlgebraicCurve.SeparableAlong K ψ)
    (n : ℤ) (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := AlgebraicCurve.algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : AlgebraicCurve.Place K F,
        n * AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        AlgebraicCurve.Differential.traceAlong ψ
          (AlgebraicCurve.Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) :=
  correspondenceNormTraceProof
    φ ψ hφ hψ hfin hN hsep n D f hf hD
end Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation
