/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Maps

/-!
# Differential pullback Along trace Along pullback Along eq trace Along pullback Along
pullback Along of swap
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.DifferentialTracePullbackSwap

open AlgebraicCurve KaehlerDifferential
open scoped TensorProduct

namespace E3WBody

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem pullbackAlong_comp (f : F →ₐ[K] F') (g : F' →ₐ[K] F'') (ω : Ω[F⁄K]) :
    Differential.pullbackAlong (g.comp f) ω =
      Differential.pullbackAlong g (Differential.pullbackAlong f ω) := by
  have hmem : ω ∈ Submodule.span F (Set.range (D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [Differential.pullbackAlong_D, Differential.pullbackAlong_D, Differential.pullbackAlong_D,
      AlgHom.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_smul,
      Differential.pullbackAlong_smul,
      hx, AlgHom.comp_apply]

theorem pullbackAlong_congr {f g : F →ₐ[K] F'} (h : ∀ x, f x = g x) :
    Differential.pullbackAlong f = Differential.pullbackAlong g := by
  have : f = g := AlgHom.ext h
  subst this; rfl

theorem pullbackAlong_traceAlong_of_conj (φ φ' : F →ₐ[K] F') (hφ : SeparableAlong K φ)
    (hφ' : SeparableAlong K φ') (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hconj : ∀ x : F, w' (φ x) = φ' (w x)) (η : Ω[F'⁄K]) :
    Differential.pullbackAlong (w : F →ₐ[K] F) (Differential.traceAlong φ η) =
      Differential.traceAlong φ' (Differential.pullbackAlong (w' : F' →ₐ[K] F') η) := by
  have htrace : ∀ u : F',
      (letI := algebraAlong φ'; Algebra.trace F F' (w' u)) =
        w (letI := algebraAlong φ; Algebra.trace F F' u) := by
    intro u
    have he : RingHom.comp (@algebraMap F F' _ _ (algebraAlong φ')) ↑(w : F ≃+* F) =
        RingHom.comp ↑(w' : F' ≃+* F') (@algebraMap F F' _ _ (algebraAlong φ)) := by
      ext x
      exact (hconj x).symm
    have := @Algebra.trace_eq_of_equiv_equiv F F' F F' _ _ _ _ (algebraAlong φ) (algebraAlong φ')
      (w : F ≃+* F) (w' : F' ≃+* F') he u
    rw [this]
    exact (RingEquiv.apply_symm_apply (w : F ≃+* F) _).symm
  let := algebraAlong φ
  have := isScalarTower_along φ
  have : Algebra.IsSeparable F F' := hφ
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
    have h1 : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F') (u ⊗ₜ ω) =
        u • Differential.pullbackAlong φ ω := by
      rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
        KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [h1, Differential.traceAlong_smul_pullbackAlong φ hφ]
    rw [Differential.pullbackAlong_smul]
    rw [Differential.pullbackAlong_smul, ← pullbackAlong_comp,
      pullbackAlong_congr (f := (w' : F' →ₐ[K] F').comp φ) (g := φ'.comp (w : F →ₐ[K] F))
        (fun x => by simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]; exact hconj x),
      pullbackAlong_comp, Differential.traceAlong_smul_pullbackAlong φ' hφ']
    change _ = (letI := algebraAlong φ'; Algebra.trace F F' (w' u)) • _
    rw [htrace]
    rfl

end E3WBody
end AlgebraicCurves.Differentials.Proofs.DifferentialTracePullbackSwap

namespace AlgebraicCurve.Differential

open _root_.AlgebraicCurves.Differentials.Proofs.DifferentialTracePullbackSwap
open _root_.AlgebraicCurve _root_.KaehlerDifferential
open scoped _root_.TensorProduct


theorem pullbackAlong_traceAlong_pullbackAlong_eq_traceAlong_pullbackAlong_pullbackAlong_of_swap
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (α β : F →ₐ[K] F') (hα : SeparableAlong K α) (hβ : SeparableAlong K β)
    (w : F ≃ₐ[K] F) (w' : F' ≃ₐ[K] F')
    (hswapα : ∀ x : F, w' (α x) = β (w x)) (hswapβ : ∀ x : F, w' (β x) = α (w x))
    (ω : Ω[F⁄K]) :
    Differential.pullbackAlong w.toAlgHom (Differential.traceAlong α (Differential.pullbackAlong β
      ω)) =
      Differential.traceAlong β (Differential.pullbackAlong α (Differential.pullbackAlong
        w.toAlgHom ω)) := by
  have h := E3WBody.pullbackAlong_traceAlong_of_conj α β hα hβ w w' hswapα
    (Differential.pullbackAlong β ω)
  rw [h, ← E3WBody.pullbackAlong_comp,
    E3WBody.pullbackAlong_congr (f := (w' : F' →ₐ[K] F').comp β) (g := α.comp (w : F →ₐ[K] F))
      (fun x => by simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]; exact hswapβ x),
    E3WBody.pullbackAlong_comp]
end AlgebraicCurve.Differential
end ProofImplementation
