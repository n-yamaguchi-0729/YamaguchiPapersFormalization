/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.OverDVR
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableClosure
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_mul_inertiaDeg_bifiber
import Nyll.AlgebraicCurves.Places.Place_exists_restrict_eq
import Nyll.AlgebraicCurves.Places.Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
import Nyll.AlgebraicCurves.Places.Place_ramificationIndexAlong_comp
import Nyll.AlgebraicCurves.Places.Place_inertiaDegAlong_comp
import Nyll.AlgebraicCurves.Divisors.Maps
import Mathlib.FieldTheory.Separable

/-!
# Place sum ramification Index mul inertia Deg exchange
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange

open _root_.AlgebraicCurve

namespace BifibreW2

section AlongBridge

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem inertiaDegAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by
  subst h; rfl

variable [Algebra F F'] [IsScalarTower K F F']

theorem isIntegral_toAlgHom [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

end AlongBridge

section Tower

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

theorem toAlgHom_comp_toAlgHom :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) =
      IsScalarTower.toAlgHom K F M :=
  AlgHom.ext fun x => (IsScalarTower.algebraMap_apply F E M x).symm

theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M]
    [Algebra.IsIntegral F M] (W : Place K M) : (W.restrict E).restrict F = W.restrict F :=
  Place.ext (by
    simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])

end Tower

end BifibreW2

section TowerRows

variable {K F E M : Type*} [Field K] [Field F] [Field E] [Field M]
    [Algebra K F] [Algebra K E] [Algebra K M] [Algebra F E] [Algebra E M] [Algebra F M]
    [IsScalarTower F E M] [IsScalarTower K F E] [IsScalarTower K E M] [IsScalarTower K F M]

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
theorem AlgebraicCurve.Place.ramificationIndex_eq_mul_ramificationIndex_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F := by
  have h := Place.ramificationIndexAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreW2.isIntegral_toAlgHom BifibreW2.isIntegral_toAlgHom
    (by rw [BifibreW2.toAlgHom_comp_toAlgHom]
        have : Algebra.IsIntegral F M := Algebra.IsIntegral.trans E
        exact BifibreW2.isIntegral_toAlgHom) W
  rw [BifibreW2.toAlgHom_comp_toAlgHom] at h
  exact h

open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
theorem AlgebraicCurve.Place.inertiaDeg_eq_mul_inertiaDeg_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M] (W : Place K M) :
    W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F := by
  have h := Place.inertiaDegAlong_comp (IsScalarTower.toAlgHom K F E)
    (IsScalarTower.toAlgHom K E M) BifibreW2.isIntegral_toAlgHom BifibreW2.isIntegral_toAlgHom
    (by rw [BifibreW2.toAlgHom_comp_toAlgHom]; exact BifibreW2.isIntegral_toAlgHom) W
  rw [BifibreW2.inertiaDegAlong_congr BifibreW2.toAlgHom_comp_toAlgHom _
    BifibreW2.isIntegral_toAlgHom] at h
  exact h

end TowerRows

namespace BifibreW2

section Envelope

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- The normal closure of the field extension inside the chosen algebraic closure. -/
abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))

theorem isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsGalois F (Env F E) := by
  have : Normal F (AlgebraicClosure E) := IsAlgClosure.normal F _
  have : ∀ f : E →ₐ[F] AlgebraicClosure E, Algebra.IsSeparable F f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  have : Algebra.IsSeparable F (Env F E) :=
    IntermediateField.isSeparable_iSup (F := F) (E := AlgebraicClosure E)
      (t := fun f : E →ₐ[F] AlgebraicClosure E => f.fieldRange)
  exact ⟨⟩

variable (R : Type*) [Field R] [Algebra R E]

/-- The base-ring algebra structure on the normal closure induced through the extension field. -/
@[reducible] noncomputable def algebraEnv : Algebra R (Env F E) :=
  ((algebraMap E (Env F E)).comp (algebraMap R E)).toAlgebra

theorem isScalarTower_env_mid : letI := algebraEnv F E R; IsScalarTower R E (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isScalarTower_env_base [Algebra F R] [IsScalarTower F R E] :
    letI := algebraEnv F E R; IsScalarTower F R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    change algebraMap F (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap F R x))
    rw [← IsScalarTower.algebraMap_apply F R E x,
      ← IsScalarTower.algebraMap_apply F E (AlgebraicClosure E) x])

variable (K : Type*) [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]

theorem isScalarTower_env_bot [Algebra K R] [IsScalarTower K R E] :
    letI := algebraEnv F E R; IsScalarTower K R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    change algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap K R x))
    rw [← IsScalarTower.algebraMap_apply K R E x,
      ← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])
omit [Algebra R E] in
theorem isScalarTower_env_const : IsScalarTower K E (Env F E) :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    change algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap K E x)
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

end Envelope

theorem exchange_of_isGalois {K F F₁ F₂ E : Type*} (M : Type*)
    [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M]
    [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M]
    [IsScalarTower K E M]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M]
    [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  have hB := AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber M hgen hLD v w₁ w₂
    hw₁ hw₂ T hT
  have hsum : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂) *
        (w₁.ramificationIndex F * w₂.inertiaDeg F) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨h₁, h₂⟩ := (hT W).mp hW
    rw [Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := F₁) W, h₁,
      Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) W, h₂]
    ring
  have he₁ : 0 < w₁.ramificationIndex F := Place.ramificationIndex_pos (F := F) w₁
  have hf₂ : 0 < w₂.inertiaDeg F := by
    have : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
    have : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) w₂
    have hPF : P.restrict F = v := by rw [← restrict_restrict (E := F₂) P, hP, hw₂]
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P hPF
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) P
    rw [hP] at hf
    have hne : Module.finrank F M ≠ 0 := Module.finrank_pos.ne'
    rw [← hTC, hf] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos he₁ hf₂)
  rw [← hsum, hB]
  ring

end BifibreW2

open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
open BifibreW2 in
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  let : Algebra F₁ (Env F E) := algebraEnv F E F₁
  let : Algebra F₂ (Env F E) := algebraEnv F E F₂
  have : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  have : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  have : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  have : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  have : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  have : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  have : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  have : IsGalois F (Env F E) := isGalois_env F E
  exact AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber (Env F E) hgen hLD v w₁ w₂
    hw₁ hw₂ T hT

open BifibreW2 in
theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  let : Algebra F₁ (Env F E) := algebraEnv F E F₁
  let : Algebra F₂ (Env F E) := algebraEnv F E F₂
  have : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  have : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  have : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  have : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  have : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  have : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  have : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  have : IsGalois F (Env F E) := isGalois_env F E
  exact exchange_of_isGalois (Env F E) hgen hLD v w₁ w₂ hw₁ hw₂ T hT
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong
