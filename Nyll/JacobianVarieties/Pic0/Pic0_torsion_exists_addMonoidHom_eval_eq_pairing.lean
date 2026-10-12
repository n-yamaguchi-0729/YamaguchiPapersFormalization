/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.WeilPairing.Datum
import Nyll.JacobianVarieties.Autoduality.Cohomology
import Nyll.JacobianVarieties.Pic0.Pic0_torsion_exists_forall_ord_eq_mul
import Nyll.JacobianVarieties.WeilPairing.WeilDatum_pairing_eq_of_isPrincipal_sub
import Nyll.JacobianVarieties.WeilPairing.WeilDatum_addLeft_pairing
import Nyll.JacobianVarieties.WeilPairing.WeilDatum_symm_pairing
import Nyll.JacobianVarieties.WeilPairing.WeilDatum_pairing_ne_zero

/-!
# Torsion evaluation through Weil pairings

Constructs the additive map from torsion divisor classes to characters whose
evaluation agrees with the Weil pairing of any representing divisor data.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.TorsionEvaluation


noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem isPrincipal_sub_of_mk_eq_i {A B : Divisor.degZero (K := K) (F := F)}
    (h : Pic0.mk A = Pic0.mk B) :
    Divisor.IsPrincipal ((A : Divisor K F) - (B : Divisor K F)) := by
  have hsub0 : Pic0.mk (A - B) = 0 := by
    change QuotientAddGroup.mk (A - B) = 0
    rw [QuotientAddGroup.mk_sub, sub_eq_zero]
    exact h
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hsub0
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have hcoe : ((A - B : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (A : Divisor K F) - (B : Divisor K F) := rfl
  rw [hcoe] at hmem
  exact Divisor.mem_principal.mp hmem

private theorem evalFun_one_i (D : Divisor K F) : Divisor.evalFun (1 : F) D = 1 := by
  rw [Divisor.evalFun_def]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Place.evalAt_one, one_zpow]

namespace WeilDatum
open _root_.AlgebraicCurve.WeilDatum
open _root_.AlgebraicCurve.WeilDatum

variable {n : ℕ}

private theorem _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_left_i (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₁) :=
  ⟨d.f₁, d.f₁_ne_zero, fun v => by rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]⟩

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.isPrincipal_smul_right_i (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₂) :=
  d.symm.isPrincipal_smul_left_i

open _root_.AlgebraicCurve.WeilDatum
private theorem degree_eq_zero_of_isPrincipal_i [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.IsPrincipal D) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDv⟩ := hD
  obtain ⟨D', hD'v, hD'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hDv v, hD'v v]
  exact hDD' ▸ hD'deg

private theorem _root_.AlgebraicCurve.WeilDatum.degree_D₁_eq_zero_i [HasPrincipalDivisors K F]
    (d : WeilDatum K F n) (hn : n ≠ 0) :
    Divisor.degree d.D₁ = 0 := by
  have h := degree_eq_zero_of_isPrincipal_i d.isPrincipal_smul_left_i
  rw [map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.degree_D₂_eq_zero_i [HasPrincipalDivisors K F]
    (d : WeilDatum K F n) (hn : n ≠ 0) :
    Divisor.degree d.D₂ = 0 :=
  d.symm.degree_D₁_eq_zero_i hn

open _root_.AlgebraicCurve.WeilDatum
section ClassLayer

variable [NeZero n] [HasPrincipalDivisors K F]

private def _root_.AlgebraicCurve.WeilDatum.degZeroLeft_i (d : WeilDatum K F n) :
    Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₁, Divisor.mem_degZero.mpr (d.degree_D₁_eq_zero_i (NeZero.ne n))⟩

open _root_.AlgebraicCurve.WeilDatum
private def _root_.AlgebraicCurve.WeilDatum.degZeroRight_i (d : WeilDatum K F n) :
    Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₂, Divisor.mem_degZero.mpr (d.degree_D₂_eq_zero_i (NeZero.ne n))⟩

open _root_.AlgebraicCurve.WeilDatum
theorem coe_degZeroLeft_i (d : WeilDatum K F n) :
    (d.degZeroLeft_i : Divisor K F) = d.D₁ := rfl

theorem coe_degZeroRight_i (d : WeilDatum K F n) :
    (d.degZeroRight_i : Divisor K F) = d.D₂ := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem mk_mem_torsion_i (D : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F))) :
    Pic0.mk D ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion]
  have h1 : (n : ℤ) • Pic0.mk D = Pic0.mk ((n : ℤ) • D) := by
    change (n : ℤ) • (QuotientAddGroup.mk D) = QuotientAddGroup.mk ((n : ℤ) • D)
    exact (QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D (n : ℤ)).symm
  rw [h1]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  have hcoe : (((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (n : ℤ) • (D : Divisor K F) := rfl
  change ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
  rw [AddSubgroup.mem_addSubgroupOf, hcoe]
  exact Divisor.mem_principal.mpr h

private def _root_.AlgebraicCurve.WeilDatum.classLeft_i (d : WeilDatum K F n) :
    Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroLeft_i, mk_mem_torsion_i d.degZeroLeft_i (by
    rw [coe_degZeroLeft_i]; exact d.isPrincipal_smul_left_i)⟩

open _root_.AlgebraicCurve.WeilDatum
private def _root_.AlgebraicCurve.WeilDatum.classRight_i (d : WeilDatum K F n) :
    Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroRight_i, mk_mem_torsion_i d.degZeroRight_i (by
    rw [coe_degZeroRight_i]; exact d.isPrincipal_smul_right_i)⟩

open _root_.AlgebraicCurve.WeilDatum
theorem classLeft_symm_i (d : WeilDatum K F n) : d.symm.classLeft_i = d.classRight_i := rfl

theorem classRight_symm_i (d : WeilDatum K F n) : d.symm.classRight_i = d.classLeft_i := rfl

theorem classLeft_addLeft_i (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classLeft_i = d.classLeft_i + d'.classLeft_i := by
  refine Subtype.ext ?_
  change Pic0.mk (d.addLeft d' hD hf).degZeroLeft_i
      = Pic0.mk d.degZeroLeft_i + Pic0.mk d'.degZeroLeft_i
  rw [← Pic0.mk_add]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem classRight_addLeft_i (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classRight_i = d.classRight_i :=
  rfl

end ClassLayer

end WeilDatum

section Datum

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

theorem exists_datum_i
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (x y : Pic0.torsion K F n) :
    ∃ d : WeilDatum K F n, d.classLeft_i = x ∧ d.classRight_i = y := by
  classical
  obtain ⟨D₁, hD₁mk, hD₁rat, -⟩ := hmove x ∅
  obtain ⟨D₂, hD₂mk, hD₂rat, hD₂avoid⟩ := hmove y (D₁ : Divisor K F).support
  obtain ⟨f₁, hf₁0, hf₁⟩ := Pic0.torsion.exists_forall_ord_eq_mul x D₁ hD₁mk
  obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂, ?_, ?_⟩,
    ?_, ?_⟩
  · intro v
    by_cases hv : (D₂ : Divisor K F) v = 0
    · exact Or.inr hv
    · refine Or.inl ?_
      by_contra hv1
      exact hD₂avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv1)
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

theorem exists_datum_pair_i
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (x x' y : Pic0.torsion K F n) :
    ∃ d d' : WeilDatum K F n, d.D₂ = d'.D₂ ∧ d.f₂ = d'.f₂ ∧
      d.classLeft_i = x ∧ d'.classLeft_i = x' ∧ d.classRight_i = y ∧ d'.classRight_i = y := by
  classical
  obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := hmove y ∅
  obtain ⟨D₁, hD₁mk, hD₁rat, hD₁avoid⟩ := hmove x (D₂ : Divisor K F).support
  obtain ⟨D₁', hD₁'mk, hD₁'rat, hD₁'avoid⟩ := hmove x' (D₂ : Divisor K F).support
  obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
  obtain ⟨f₁, hf₁0, hf₁⟩ := Pic0.torsion.exists_forall_ord_eq_mul x D₁ hD₁mk
  obtain ⟨f₁', hf₁'0, hf₁'⟩ := Pic0.torsion.exists_forall_ord_eq_mul x' D₁' hD₁'mk
  have hdisj : ∀ (D : Divisor.degZero (K := K) (F := F)),
      (∀ v ∈ (D : Divisor K F).support, v ∉ (D₂ : Divisor K F).support) →
      ∀ v : Place K F, (D : Divisor K F) v = 0 ∨ (D₂ : Divisor K F) v = 0 := by
    intro D havoid v
    by_cases hv : (D : Divisor K F) v = 0
    · exact Or.inl hv
    · refine Or.inr ?_
      by_contra hv2
      exact havoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv2)
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂,
      hdisj D₁ hD₁avoid, ?_⟩,
    ⟨(D₁' : Divisor K F), (D₂ : Divisor K F), f₁', f₂, hf₁'0, hf₂0, hf₁', hf₂,
      hdisj D₁' hD₁'avoid, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁'rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (x' : Pic0 K F)
    rw [← hD₁'mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    change Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

end Datum

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.torsion.exists_addMonoidHom_eval_eq_pairing {K F : Type*}
    [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S)) :
    ∃ hom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n),
      ∀ (d : WeilDatum K F n) (x y : Pic0.torsion K F n),
        (∃ E : Divisor.degZero (K := K) (F := F),
          (E : Divisor K F) = d.D₁ ∧ Pic0.mk E = (x : Pic0 K F)) →
        (∃ E : Divisor.degZero (K := K) (F := F),
          (E : Divisor K F) = d.D₂ ∧ Pic0.mk E = (y : Pic0 K F)) →
        (Additive.toMul (hom x)) y = d.pairing := by
  classical
  choose d₀ hd₀L hd₀R using fun x y : Pic0.torsion K F n => AlgebraicCurve.exists_datum_i hmove x y
  set pair : Pic0.torsion K F n → Pic0.torsion K F n → K := fun x y => (d₀ x y).pairing
    with hpairdef
  have compat : ∀ d : WeilDatum K F n,
      pair (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d) = d.pairing := by
    intro d
    have hL' := hd₀L (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d)
    have hR' := hd₀R (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d)
    have hmkL : Pic0.mk (WeilDatum.degZeroLeft_i
          (d₀ (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d)))
        = Pic0.mk (WeilDatum.degZeroLeft_i d) := congrArg Subtype.val hL'
    have hmkR : Pic0.mk (WeilDatum.degZeroRight_i
          (d₀ (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d)))
        = Pic0.mk (WeilDatum.degZeroRight_i d) := congrArg Subtype.val hR'
    exact WeilDatum.pairing_eq_of_isPrincipal_sub hrec hconst hmove d
      (d₀ (WeilDatum.classLeft_i d) (WeilDatum.classRight_i d))
      (AlgebraicCurve.isPrincipal_sub_of_mk_eq_i hmkL)
      (AlgebraicCurve.isPrincipal_sub_of_mk_eq_i hmkR)
  have pair_ne : ∀ x y : Pic0.torsion K F n, pair x y ≠ 0 := fun x y =>
    WeilDatum.pairing_ne_zero (d₀ x y)
  have pair_add_left : ∀ x x' y : Pic0.torsion K F n,
      pair (x + x') y = pair x y * pair x' y := by
    intro x x' y
    obtain ⟨da, da', hD₂, hf₂, hx, hx', hy, hy'⟩ := AlgebraicCurve.exists_datum_pair_i hmove x x' y
    have h1 := compat (da.addLeft da' hD₂ hf₂)
    rw [AlgebraicCurve.WeilDatum.classLeft_addLeft_i, AlgebraicCurve.WeilDatum.classRight_addLeft_i,
      WeilDatum.addLeft_pairing, hx, hx', hy] at h1
    rw [h1, ← compat da, ← compat da', hx, hx', hy, hy']
  have pair_swap_one : ∀ x y : Pic0.torsion K F n, pair x y * pair y x = 1 := by
    intro x y
    obtain ⟨d, hx, hy⟩ := AlgebraicCurve.exists_datum_i hmove x y
    have h1 := compat d
    have h2 := compat d.symm
    rw [hx, hy] at h1
    rw [AlgebraicCurve.WeilDatum.classLeft_symm_i, AlgebraicCurve.WeilDatum.classRight_symm_i, hx,
      hy] at h2
    rw [h1, h2, WeilDatum.symm_pairing]
    exact mul_inv_cancel₀ (WeilDatum.pairing_ne_zero d)
  have pair_zero_left : ∀ y : Pic0.torsion K F n, pair 0 y = 1 := by
    intro y
    obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := hmove y ∅
    obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
    set dz : WeilDatum K F n :=
      ⟨0, (D₂ : Divisor K F), 1, f₂, one_ne_zero, hf₂0,
        fun v => by simp only [Place.ord_one, Finsupp.coe_zero, Pi.zero_apply, mul_zero],
        hf₂, fun v => Or.inl rfl,
        fun v hv => by
          rcases hv with h1 | h2
          · exact absurd rfl h1
          · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with hdz
    have h1 := compat dz
    have hclassL : WeilDatum.classLeft_i dz = 0 := by
      have h0 : WeilDatum.degZeroLeft_i dz = (0 : Divisor.degZero (K := K) (F := F)) :=
        Subtype.ext rfl
      refine Subtype.ext ?_
      change Pic0.mk (WeilDatum.degZeroLeft_i dz) = ((0 : Pic0.torsion K F n) : Pic0 K F)
      rw [h0, Pic0.mk_zero, AddSubgroup.coe_zero]
    have hclassR : WeilDatum.classRight_i dz = y := by
      refine Subtype.ext ?_
      change Pic0.mk (WeilDatum.degZeroRight_i dz) = (y : Pic0 K F)
      rw [← hD₂mk]
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have hpairing : dz.pairing = 1 := by
      change Divisor.evalFun (1 : F) (D₂ : Divisor K F) / Divisor.evalFun f₂ (0 : Divisor K F) = 1
      rw [AlgebraicCurve.evalFun_one_i, Divisor.evalFun_zero, div_one]
    rw [hclassL, hclassR, hpairing] at h1
    exact h1
  have pair_zero_right : ∀ x : Pic0.torsion K F n, pair x 0 = 1 := by
    intro x
    have h1 := pair_swap_one x 0
    rw [pair_zero_left x, mul_one] at h1
    exact h1
  have pair_swap_inv : ∀ x y : Pic0.torsion K F n, pair y x = (pair x y)⁻¹ := fun x y =>
    eq_inv_of_mul_eq_one_left (pair_swap_one y x)
  have pair_add_right : ∀ x y y' : Pic0.torsion K F n,
      pair x (y + y') = pair x y * pair x y' := by
    intro x y y'
    calc pair x (y + y') = (pair (y + y') x)⁻¹ := pair_swap_inv (y + y') x
      _ = (pair y x * pair y' x)⁻¹ := by rw [pair_add_left y y' x]
      _ = (pair y x)⁻¹ * (pair y' x)⁻¹ := by rw [mul_inv]
      _ = pair x y * pair x y' := by
          rw [pair_swap_inv x y, pair_swap_inv x y', inv_inv, inv_inv]
  set chr : Pic0.torsion K F n → HomPic0Gm K F n := fun x =>
    { toFun := fun y => pair x y
      map_zero_eq_one' := pair_zero_right x
      map_add_eq_mul' := fun y y' => pair_add_right x y y' } with hchr
  have hadd : ∀ x x' : Pic0.torsion K F n,
      Additive.ofMul (chr (x + x')) = Additive.ofMul (chr x) + Additive.ofMul (chr x') := by
    intro x x'
    have h : chr (x + x') = chr x * chr x' := by
      ext y
      rw [AddChar.mul_apply]
      exact pair_add_left x x' y
    rw [h, ofMul_mul]
  refine ⟨AddMonoidHom.mk' (fun x => Additive.ofMul (chr x)) hadd, ?_⟩
  rintro d x y ⟨E₁, hE₁d, hE₁mk⟩ ⟨E₂, hE₂d, hE₂mk⟩
  have hx : x = WeilDatum.classLeft_i d := by
    have hE : E₁ = WeilDatum.degZeroLeft_i d := Subtype.ext hE₁d
    refine Subtype.ext ?_
    change (x : Pic0 K F) = Pic0.mk (WeilDatum.degZeroLeft_i d)
    rw [← hE₁mk, hE]
  have hy : y = WeilDatum.classRight_i d := by
    have hE : E₂ = WeilDatum.degZeroRight_i d := Subtype.ext hE₂d
    refine Subtype.ext ?_
    change (y : Pic0 K F) = Pic0.mk (WeilDatum.degZeroRight_i d)
    rw [← hE₂mk, hE]
  change pair x y = d.pairing
  rw [hx, hy]
  exact compat d

end
end JacobianVarieties.Pic0.Proofs.TorsionEvaluation
end ProofImplementation
