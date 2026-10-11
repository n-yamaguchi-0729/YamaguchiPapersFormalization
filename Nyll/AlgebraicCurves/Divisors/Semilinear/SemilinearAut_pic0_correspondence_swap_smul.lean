/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
# Semilinear Aut pic0 correspondence swap smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pic0_correspondence_swap_smul

open AlgebraicCurve
open scoped _root_.Pointwise

namespace SwapSmul

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable {g : SemilinearAut K F} {g' : SemilinearAut K F'}
variable {φ ψ : F →ₐ[K] F'}

/-- The two embeddings intertwine the source and target semilinear actions in the stated order. -/
def CrossIntertwines (φ ψ : F →ₐ[K] F') (g : SemilinearAut K F) (g' : SemilinearAut K F') :
    Prop :=
  ∀ x : F, g' • (φ x) = ψ (g • x)

theorem CrossIntertwines.inv (h : CrossIntertwines φ ψ g g') :
    CrossIntertwines ψ φ g⁻¹ g'⁻¹ := by
  intro x
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]

theorem restrictAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).restrictAlong ψ hψ = g • w.restrictAlong φ hφ := by
  apply Place.toValuationSubring_injective
  ext x
  change ψ x ∈ (g' • w).toValuationSubring ↔
    x ∈ (g • w.restrictAlong φ hφ).toValuationSubring
  rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, h.inv x]
  rfl

private theorem ord_smul (h : CrossIntertwines φ ψ g g') (w : Place K F') (f : F) :
    (g' • w).ord (ψ f) = w.ord (φ (g⁻¹ • f)) := by
  have : ψ f = g' • φ (g⁻¹ • f) := by rw [h, smul_inv_smul]
  rw [this, SemilinearAut.ord_smul]

theorem ramificationIndexAlong_smul (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).ramificationIndexAlong ψ = w.ramificationIndexAlong φ := by
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  change sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (g' • w).ord (ψ f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (φ f) = n}
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_smul h, hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_smul h, inv_smul_smul, hford]

/--
The ring equivalence between restricted valuation rings induced by the intertwining semilinear
automorphisms.
-/
noncomputable def restrictEquiv (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring ≃+*
      ((g' • w).restrictAlong ψ hψ).toValuationSubring where
  toFun x := ⟨g • (x : F), by
    have hx : φ (x : F) ∈ w.toValuationSubring := x.2
    change ψ (g • (x : F)) ∈ (g' • w).toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring, ← h (x : F)]
    exact ValuationSubring.smul_mem_pointwise_smul g' _ _ hx⟩
  invFun y := ⟨g⁻¹ • (y : F), by
    have hy : ψ (y : F) ∈ (g' • w).toValuationSubring := y.2
    change φ (g⁻¹ • (y : F)) ∈ w.toValuationSubring
    rw [SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hy
    rw [← h.inv (y : F)]
    exact hy⟩
  left_inv x := by ext; exact inv_smul_smul g (x : F)
  right_inv y := by ext; exact smul_inv_smul g (y : F)
  map_mul' x y := by ext; exact smul_mul' g (x : F) (y : F)
  map_add' x y := by ext; exact smul_add g (x : F) (y : F)

theorem inertiaDegAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (w : Place K F') :
    (g' • w).inertiaDegAlong ψ hψ = w.inertiaDegAlong φ hφ := by
  let iφ : Algebra (w.restrictAlong φ hφ).ResidueField w.ResidueField :=
    (letI := algebraAlong φ; have _ := isScalarTower_along φ; have _ := isIntegral_along φ hφ
     (Place.restrictResidueMap F w).toAlgebra)
  let iψ : Algebra ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField :=
    (letI := algebraAlong ψ; have _ := isScalarTower_along ψ; have _ := isIntegral_along ψ hψ
     (Place.restrictResidueMap F (g' • w)).toAlgebra)
  change Module.finrank ((g' • w).restrictAlong ψ hψ).ResidueField (g' • w).ResidueField
    = Module.finrank (w.restrictAlong φ hφ).ResidueField w.ResidueField
  refine (Algebra.finrank_eq_of_equiv_equiv
    (IsLocalRing.ResidueField.mapEquiv (restrictEquiv hφ hψ h w))
    (SemilinearAut.smulResidueRingEquiv g' w) ?_).symm
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsLocalRing.residue (g' • w).toValuationSubring
      (⟨ψ (g • (a : F)), _⟩ : (g' • w).toValuationSubring)
    = IsLocalRing.residue (g' • w).toValuationSubring
      (⟨g' • φ (a : F), _⟩ : (g' • w).toValuationSubring)
  exact congrArg (IsLocalRing.residue _) (Subtype.ext (h (a : F)).symm)

theorem pullbackAlong_smul [HasPrincipalDivisors K F'] (hφ : φ.toRingHom.IsIntegral)
    (hψ : ψ.toRingHom.IsIntegral) (h : CrossIntertwines φ ψ g g') (D : Divisor K F) :
    Divisor.pullbackAlong ψ hψ (g • D) = g' • Divisor.pullbackAlong φ hφ D := by
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    SemilinearAut.divisor_smul_apply, Divisor.pullbackAlong_apply,
    restrictAlong_smul hψ hφ h.inv w, ramificationIndexAlong_smul h.inv w]

theorem pushforwardAlong_smul (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h : CrossIntertwines φ ψ g g') (E : Divisor K F') :
    Divisor.pushforwardAlong ψ hψ (g' • E) = g • Divisor.pushforwardAlong φ hφ E := by
  induction E using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [SemilinearAut.smul_single, Divisor.pushforwardAlong_single,
      Divisor.pushforwardAlong_single, SemilinearAut.smul_single,
      restrictAlong_smul hφ hψ h w, inertiaDegAlong_smul hφ hψ h w]

theorem correspondence_smul_exchange [HasPrincipalDivisors K F']
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (h₁ : CrossIntertwines φ ψ g g') (h₂ : CrossIntertwines ψ φ g g') (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (g • D) = g • Divisor.correspondence ψ φ hψ hφ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pullbackAlong_smul hψ hφ h₂ D, pushforwardAlong_smul hφ hψ h₁]

end SwapSmul

open SwapSmul in
theorem solution {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F}
    {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : ∀ x : F, g' • (φ x) = ψ (g • x)) (h₂ : ∀ x : F, g' • (ψ x) = φ (g • x))
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [SemilinearAut.pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk,
    SemilinearAut.pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_degZeroCorrespondence, SemilinearAut.coe_degZeroSMulHom,
    SemilinearAut.coe_degZeroSMulHom, Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul_exchange hφ hψ h₁ h₂ (D : Divisor K F)

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pic0_correspondence_swap_smul
end ProofImplementation


open AlgebraicCurve

open AlgebraicCurves.Divisors.Semilinear.Proofs in
open SemilinearAut_pic0_correspondence_swap_smul
  renaming solution → semilinearProof in
theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul {K F F' : Type*} [Field K]
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F}
    {g' : SemilinearAut K F'} [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    (h₁ : ∀ x : F, g' • (φ x) = ψ (g • x)) (h₂ : ∀ x : F, g' • (ψ x) = φ (g • x))
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ (g • c)
      = g • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ c := by
  exact semilinearProof (K := K) (F := F) (F' := F') (g := g) (g' := g') (φ := φ) (ψ := ψ)
    (hφ := hφ) (hψ := hψ) (hFIφ := hFIφ) (hfinψ := hfinψ) (hNψ := hNψ) (hFIψ := hFIψ)
    (hfinφ := hfinφ) (hNφ := hNφ) (h₁ := h₁) (h₂ := h₂) (c := c)
