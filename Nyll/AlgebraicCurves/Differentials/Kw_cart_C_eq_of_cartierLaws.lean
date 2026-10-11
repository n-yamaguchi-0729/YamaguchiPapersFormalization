/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.CartierCoordinates
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Kw_cart_C_pow_smul_D_eq_zero
import Nyll.AlgebraicCurves.Differentials.Kw_cart_C_pow_pred_smul_D
import Nyll.AlgebraicCurves.Differentials.CartierOperator_existsUnique

/-!
# Kw cart C eq of cartier Laws
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Kw_cart_C_eq_of_cartierLaws
attribute [-simp] AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero
  AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one

open AlgebraicCurve.KwCart AlgebraicCurve.KwPke

theorem _root_.AlgebraicCurve.kw_cart_C_eq_of_cartierLaws {K F : Type*} [Field K] [Field F]
  [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K] [CharP F p]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ y : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield y)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (ω : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg ω = C ω := by
  let C' : Ω[F⁄K] →+ Ω[F⁄K] :=
    { toFun := kw_cart_C (K := K) t hdt hspan hsep hdeg
      map_zero' := by
        have h := kw_cart_C_add (K := K) t hdt hspan hsep hdeg 0 0
        rw [add_zero] at h
        exact left_eq_add.mp h
      map_add' := kw_cart_C_add (K := K) t hdt hspan hsep hdeg }
  have hC' : (∀ (f : F) (ω : Ω[F⁄K]), C' (f ^ p • ω) = f • C' ω) ∧
      (∀ f : F, C' (KaehlerDifferential.D K F f) = 0) ∧
      (∀ f : F, C' (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f) :=
    ⟨fun f ω => kw_cart_C_semilinear (K := K) t hdt hspan hsep hdeg f ω,
     fun f => by
       have hp : p.Prime := Fact.out
       have h := AlgebraicCurve.kw_cart_C_pow_smul_D_eq_zero (K := K) (ℓ := p) t hdt hspan hsep
         hdeg f
         (i := 0) (by have := hp.two_le; omega)
       (simp only [pow_zero, one_smul] at h; exact h),
     fun f => AlgebraicCurve.kw_cart_C_pow_pred_smul_D (K := K) (ℓ := p) t hdt hspan hsep hdeg f⟩
  have huniq := (AlgebraicCurve.cartierOperator_existsUnique (K := K) (F := F) p x).unique hC'
    ⟨hsemi, hker, hlog⟩
  exact DFunLike.congr_fun huniq ω
end AlgebraicCurves.Differentials.Proofs.Kw_cart_C_eq_of_cartierLaws
end ProofImplementation
