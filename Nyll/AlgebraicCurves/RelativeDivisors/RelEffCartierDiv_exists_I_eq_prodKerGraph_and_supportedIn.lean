/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn

/-!
# Rel Eff Cartier Div exists I eq prod Ker Graph and supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FltWs21
namespace M10b

theorem supportedIn_ofPoint {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens)
    {T : Scheme.{u}} {g : T ⟶ S} (a : T ⟶ 𝒞) (ha : a ≫ f = g) (haU : Set.range a.base ⊆ (U : Set
      𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  intro x hx
  rw [RelEffCartierDiv.ofPoint_I] at hx
  have hx' : x ∈ ((graphOver f a ha).ker.support : Set ↥(pullback f g)) := hx
  rw [Scheme.Hom.support_ker, (IsClosedImmersion.isClosedEmbedding (graphOver f a
    ha)).isClosed_range.closure_eq] at hx'
  obtain ⟨t, rfl⟩ := hx'
  change pullback.fst f g (graphOver f a ha t) ∈ U
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨t, rfl⟩

end FltWs21.M10b

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι
      ≫ f)]
    {e : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (a : Fin e → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g)
    (haU : ∀ i, Set.range (a i).base ⊆ (U : Set 𝒞)) :
    ∃ D : RelEffCartierDiv f e g, D.I = prodKerGraph f a ha ∧ D.SupportedIn U := by
  induction e with
  | zero =>
      refine ⟨RelEffCartierDiv.empty f g, ?_, ?_⟩
      · rw [RelEffCartierDiv.empty_I, prodKerGraph_zero]
      · intro x hx
        rw [RelEffCartierDiv.empty_I] at hx
        have : x ∈ ((⊤ : (pullback f g).IdealSheafData).support : Set ↥(pullback f g)) := hx
        rw [Scheme.IdealSheafData.support_top] at this
        exact False.elim this
  | succ e ih =>
      obtain ⟨D', hD'I, hD'U⟩ := ih (fun i => a i.succ) (fun i => ha i.succ) (fun i => haU i.succ)
      obtain ⟨F, hFI, hFU⟩ :=
        AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U D'
        (RelEffCartierDiv.ofPoint f (a 0) (ha 0)) hD'U (FltWs21.M10b.supportedIn_ofPoint U (a 0)
          (ha 0) (haU 0))
      refine ⟨F, ?_, hFU⟩
      rw [hFI, hD'I, RelEffCartierDiv.ofPoint_I, prodKerGraph_succ, mul_comm]
end RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
end AlgebraicCurves.RelativeDivisors.Proofs
end ProofImplementation
