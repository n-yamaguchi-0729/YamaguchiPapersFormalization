/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_sum_galois_smul_eq_pullback_pushforward.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Places.Place_exists_algEquiv_smul_eq_of_restrict_eq
import Nyll.AlgebraicCurves.Places.Place_restrict_ofAlgAut_smul
import Nyll.AlgebraicCurves.Places.Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg

/-!
# Divisor sum galois smul eq pullback pushforward
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_sum_galois_smul_eq_pullback_pushforward

noncomputable section

namespace GalTraceDiv

open AlgebraicCurve AlgebraicCurve.SemilinearAut Finset

variable {K F M : Type*} [Field K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]

/-- The semilinear automorphism obtained by restricting an automorphism of the extension field. -/
abbrev act (σ : M ≃ₐ[F] M) : SemilinearAut K M := ofAlgAut (σ.restrictScalars K)

theorem act_mul (σ τ : M ≃ₐ[F] M) : act (K := K) (σ * τ) = act (K := K) σ * act (K := K) τ := by
  change ofAlgAut ((σ * τ).restrictScalars K) = ofAlgAut (σ.restrictScalars K) * ofAlgAut
    (τ.restrictScalars K)
  rw [← map_mul]
  congr 1

theorem act_one : act (K := K) (1 : M ≃ₐ[F] M) = 1 := by
  change ofAlgAut ((1 : M ≃ₐ[F] M).restrictScalars K) = 1
  rw [← map_one (ofAlgAut (K := K) (F := M))]
  congr 1

theorem act_smul_smul (σ τ : M ≃ₐ[F] M) (W : Place K M) :
    act (K := K) σ • (act (K := K) τ • W) = act (K := K) (σ * τ) • W := by
  rw [act_mul, mul_smul]

theorem act_one_smul (W : Place K M) : act (K := K) (1 : M ≃ₐ[F] M) • W = W := by
  rw [act_one, one_smul]

theorem act_algebraMap (σ : M ≃ₐ[F] M) (f : F) :
    act (K := K) σ • algebraMap F M f = algebraMap F M f := by
  change (σ.restrictScalars K) (algebraMap F M f) = algebraMap F M f
  rw [AlgEquiv.restrictScalars_apply]
  exact σ.commutes f

theorem ramificationIndex_act_smul (σ : M ≃ₐ[F] M) (W : Place K M) :
    (act (K := K) σ • W).ramificationIndex F = W.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => exists_congr fun f => and_congr_right fun _ => ?_
  have h := SemilinearAut.ord_smul (act (K := K) σ) W (algebraMap F M f)
  have h2 : (act (K := K) σ • W).ord (algebraMap F M f) = W.ord (algebraMap F M f) := by
    convert h using 2
    exact (act_algebraMap σ f).symm
  rw [h2]

section Galois

variable [FiniteDimensional F M] [IsGalois F M]

omit [FiniteDimensional F M] in
theorem restrict_act_smul (σ : M ≃ₐ[F] M) (W : Place K M) :
    (act (K := K) σ • W).restrict F = W.restrict F :=
  Place.restrict_ofAlgAut_smul σ W

theorem exists_act_smul_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    ∃ σ : M ≃ₐ[F] M, act (K := K) σ • W = W' :=
  Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h

/-- The finite set of automorphisms carrying the first place to the second. -/
def transporter (W W' : Place K M) : Finset (M ≃ₐ[F] M) :=
  haveI := Classical.decEq (Place K M)
  Finset.univ.filter (fun σ => act (K := K) σ • W = W')
omit [IsGalois F M] in
theorem mem_transporter {W W' : Place K M} {σ : M ≃ₐ[F] M} :
    σ ∈ transporter (F := F) W W' ↔ act (K := K) σ • W = W' := by
  unfold transporter
  simp
omit [IsGalois F M] in
theorem transporter_eq_image [DecidableEq (M ≃ₐ[F] M)] (W W' : Place K M) (τ : M ≃ₐ[F] M)
    (hτ : act (K := K) τ • W = W') :
    transporter (F := F) W W' = (transporter (F := F) W W).image (fun σ => τ * σ) := by
  ext σ
  rw [mem_transporter, Finset.mem_image]
  constructor
  · intro h
    refine ⟨τ⁻¹ * σ, ?_, by group⟩
    rw [mem_transporter, ← act_smul_smul, h, ← hτ, act_smul_smul, inv_mul_cancel, act_one_smul]
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mem_transporter] at hρ
    rw [← act_smul_smul, hρ, hτ]
omit [IsGalois F M] in
theorem card_transporter_eq (W W' : Place K M) (τ : M ≃ₐ[F] M) (hτ : act (K := K) τ • W = W') :
    (transporter (F := F) W W').card = (transporter (F := F) W W).card := by
  classical
  rw [transporter_eq_image W W' τ hτ]
  exact Finset.card_image_of_injective _ (mul_right_injective τ)

theorem card_univ_eq_sum (W : Place K M) :
    (Finset.univ : Finset (M ≃ₐ[F] M)).card
      = ∑ W' ∈ (W.restrict F).fiberOver M, (transporter (F := F) W W').card := by
  classical
  have H : ((Finset.univ : Finset (M ≃ₐ[F] M)) : Set (M ≃ₐ[F] M)).MapsTo
      (fun σ => act (K := K) σ • W) ((W.restrict F).fiberOver M) := by
    intro σ _
    rw [Finset.mem_coe, Place.mem_fiberOver, restrict_act_smul]
  rw [Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun W' _ => ?_
  unfold transporter
  congr 1

theorem card_transporter (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    (transporter (F := F) W W').card = W.ramificationIndex F * W.inertiaDeg F := by
  classical
  obtain ⟨τ, hτ⟩ := exists_act_smul_eq (K := K) W W' h
  rw [card_transporter_eq W W' τ hτ]
  have hsum := card_univ_eq_sum (K := K) (F := F) W
  have hconst : ∀ W'' ∈ (W.restrict F).fiberOver M,
      (transporter (F := F) W W'').card = (transporter (F := F) W W).card := by
    intro W'' hW''
    obtain ⟨ρ, hρ⟩ := exists_act_smul_eq (K := K) W W'' ((Place.mem_fiberOver _).mp hW'')
    exact card_transporter_eq W W'' ρ hρ
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hsum
  have hG : (Finset.univ : Finset (M ≃ₐ[F] M)).card = Module.finrank F M := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank F M
  have hef := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W.restrict F) W rfl
  rw [hG, ← hef] at hsum
  have hpos : 0 < ((W.restrict F).fiberOver M).card :=
    Finset.card_pos.mpr ⟨W, Place.restrict_mem_fiberOver W⟩
  exact (Nat.eq_of_mul_eq_mul_left hpos hsum).symm

theorem ramificationIndex_mul_inertiaDeg_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    W'.ramificationIndex F * W'.inertiaDeg F = W.ramificationIndex F * W.inertiaDeg F := by
  have h1 := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W.restrict F) W rfl
  have h2 := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W.restrict F) W' h
  have hpos : 0 < ((W.restrict F).fiberOver M).card :=
    Finset.card_pos.mpr ⟨W, Place.restrict_mem_fiberOver W⟩
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.trans h1.symm)

theorem ramificationIndex_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    W'.ramificationIndex F = W.ramificationIndex F := by
  obtain ⟨τ, hτ⟩ := exists_act_smul_eq (K := K) W W' h
  rw [← hτ, ramificationIndex_act_smul]

theorem inertiaDeg_mul_ramificationIndex_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    W.inertiaDeg F * W'.ramificationIndex F = W.ramificationIndex F * W.inertiaDeg F := by
  rw [ramificationIndex_eq W W' h, mul_comm]

variable [HasPrincipalDivisors K M]

theorem sum_smul_single (W : Place K M) (n : ℤ) :
    ∑ σ : M ≃ₐ[F] M, act (K := K) σ • (Finsupp.single W n : Divisor K M)
      = Divisor.pullback M (Divisor.pushforward F (Finsupp.single W n)) := by
  classical
  rw [Divisor.pushforward_single, Divisor.pullback_single, Place.fiber_eq_fiberOver]
  simp only [smul_single]
  have H : ((Finset.univ : Finset (M ≃ₐ[F] M)) : Set (M ≃ₐ[F] M)).MapsTo
      (fun σ => act (K := K) σ • W) ((W.restrict F).fiberOver M) := by
    intro σ _
    rw [Finset.mem_coe, Place.mem_fiberOver, restrict_act_smul]
  rw [← Finset.sum_fiberwise_of_maps_to H]
  refine Finset.sum_congr rfl fun W' hW' => ?_
  have hW'' : W'.restrict F = W.restrict F := (Place.mem_fiberOver _).mp hW'
  have hin : ∀ σ ∈ (Finset.univ : Finset (M ≃ₐ[F] M)).filter (fun σ : M ≃ₐ[F] M => act (K := K) σ •
    W = W'),
      Finsupp.single (act (K := K) σ • W) n = (Finsupp.single W' n : Divisor K M) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [hσ.2]
  rw [Finset.sum_congr rfl hin, Finset.sum_const]
  have hcard : ((Finset.univ : Finset (M ≃ₐ[F] M)).filter (fun σ : M ≃ₐ[F] M => act (K := K) σ • W
    = W')).card
      = W.ramificationIndex F * W.inertiaDeg F := by
    have := card_transporter (K := K) (F := F) W W' hW''
    unfold transporter at this
    convert this
  rw [hcard, Finsupp.smul_single, nsmul_eq_mul]
  congr 1
  have h2 := congrArg (fun m : ℕ => (m : ℤ))
    (inertiaDeg_mul_ramificationIndex_eq (K := K) (F := F) W W' hW'')
  push_cast at h2 ⊢
  linear_combination (n : ℤ) * h2.symm

theorem main (D : Divisor K M) :
    ∑ σ : M ≃ₐ[F] M, act (K := K) σ • D = Divisor.pullback M (Divisor.pushforward F D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE =>
      rw [map_add, map_add, ← hD, ← hE, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun σ _ => smul_add _ _ _
  | single W n => exact sum_smul_single W n

end Galois

end GalTraceDiv

end

theorem _root_.AlgebraicCurve.Divisor.sum_galois_smul_eq_pullback_pushforward
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [FiniteDimensional F F'] [IsGalois F F']
    [AlgebraicCurve.HasPrincipalDivisors K F'] (D : AlgebraicCurve.Divisor K F') :
    ∑ σ : F' ≃ₐ[F] F', AlgebraicCurve.SemilinearAut.ofAlgAut (σ.restrictScalars K) • D
      = AlgebraicCurve.Divisor.pullback F' (AlgebraicCurve.Divisor.pushforward F D) :=
  GalTraceDiv.main D
end AlgebraicCurves.Divisors.Proofs.Divisor_sum_galois_smul_eq_pullback_pushforward
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
