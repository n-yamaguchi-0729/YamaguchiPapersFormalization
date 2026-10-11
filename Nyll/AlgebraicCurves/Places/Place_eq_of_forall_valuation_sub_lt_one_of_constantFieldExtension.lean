/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.Rational.Basic
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.FunctionFields.LinearIndependent_of_constantFieldExtension
import Nyll.AlgebraicCurves.Places.Place_exists_of_valuationSubring
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndex_eq_finrank
import Nyll.AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeOfPoint_algebraMap

/-!
# Place eq of forall valuation sub lt one of constant Field Extension
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

open _root_.AlgebraicCurve
open scoped TensorProduct IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CentredPlaceRigidity
open _root_.AlgebraicCurve

section General

variable {E FE : Type*} [Field E] [Field FE] [Algebra E FE]

theorem mem_of_valuation_lt_one (P : Place E FE) {y : FE}
    (hy : P.toValuationSubring.valuation y < 1) : y ∈ P.toValuationSubring :=
  (ValuationSubring.valuation_le_one_iff _ _).mp hy.le

theorem adicValuation_lt_one_of_valuation_lt_one (P : Place E FE) {y : FE}
    (hy : P.toValuationSubring.valuation y < 1) : P.adicValuation y < 1 := by
  have hmem := mem_of_valuation_lt_one P hy
  have h := (ValuationSubring.valuation_lt_one_iff P.toValuationSubring ⟨y, hmem⟩).mpr hy
  exact (P.mem_maximalIdeal_iff_adicValuation_lt_one ⟨y, hmem⟩).mp h

theorem ord_ne_zero_of_valuation_lt_one (P : Place E FE) {y : FE} (hy0 : y ≠ 0)
    (hy : P.toValuationSubring.valuation y < 1) : P.ord y ≠ 0 := fun h =>
  (adicValuation_lt_one_of_valuation_lt_one P hy).ne
    ((P.ord_eq_zero_iff_adicValuation_eq_one hy0).mp h)

theorem eq_zero_of_valuation_algebraMap_lt_one (P : Place E FE) {c : E}
    (hc : P.toValuationSubring.valuation (algebraMap E FE c) < 1) : c = 0 := by
  by_contra h
  have hu : IsUnit (algebraMap E P.toValuationSubring c) := (IsUnit.mk0 c h).map _
  have h1 := (ValuationSubring.valuation_eq_one_iff _ _).mp hu
  rw [Place.coe_algebraMap] at h1
  exact hc.ne h1

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F FE]

theorem centre_unique (P : Place E FE) {σ τ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (σ f)) < 1)
    (hτ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (τ f)) < 1) :
    σ = τ := by
  ext f
  have h : P.toValuationSubring.valuation (algebraMap E FE (τ f - σ f)) < 1 := by
    have := Valuation.map_sub P.toValuationSubring.valuation
      (algebraMap F FE f - algebraMap E FE (σ f)) (algebraMap F FE f - algebraMap E FE (τ f))
    rw [sub_sub_sub_cancel_left, ← map_sub] at this
    exact this.trans_lt (max_lt (hσ f) (hτ f))
  exact (sub_eq_zero.mp (eq_zero_of_valuation_algebraMap_lt_one P h)).symm

theorem algebraMap_mem_of_centred (P : Place E FE) {σ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (σ f)) < 1)
    (f : F) : algebraMap F FE f ∈ P.toValuationSubring := by
  have h := add_mem (mem_of_valuation_lt_one P (hσ f)) (P.algebraMap_mem' (σ f))
  rwa [sub_add_cancel] at h

end General

section Transcendental

theorem linearIndependent_pow_iff_transcendental {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (x : A) :
    LinearIndependent R (fun n : ℕ => x ^ n) ↔ Transcendental R x := by
  have h := Polynomial.linearIndependent_powers_iff_aeval (Algebra.lmul R A x : A →ₗ[R] A) (1 : A)
  have h1 : (fun n : ℕ => ((Algebra.lmul R A x : A →ₗ[R] A) ^ n) (1 : A)) = fun n => x ^ n := by
    funext n
    rw [← map_pow, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]
  rw [h1] at h
  rw [h, Transcendental, isAlgebraic_iff_not_injective, not_not, injective_iff_map_eq_zero]
  refine forall_congr' fun p => ?_
  rw [Polynomial.aeval_algHom_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', mul_one]

end Transcendental

section Span

theorem span_eq_top_of_adjoin_eq_top {E L M : Type*} [Field E] [Field L] [Field M] [Algebra E L]
    [Algebra L M] [Algebra E M] [IsScalarTower E L M] {ι : Type*} [Finite ι] (b : ι → M)
    (hmul : ∀ i j, b i * b j ∈ Submodule.span L (Set.range b))
    (h1 : (1 : M) ∈ Submodule.span L (Set.range b))
    {T : Set M} (hT : T ⊆ Submodule.span L (Set.range b))
    (hgen : IntermediateField.adjoin E T = ⊤) :
    Submodule.span L (Set.range b) = ⊤ := by
  set S := Submodule.span L (Set.range b) with hS
  have : FiniteDimensional L S := FiniteDimensional.span_of_finite L (Set.finite_range b)
  have hmul' : ∀ s ∈ S, ∀ s' ∈ S, s * s' ∈ S := by
    refine Submodule.mul_le.mp ?_
    rw [hS, Submodule.span_mul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    exact hmul i j
  have hinv : ∀ s ∈ S, s⁻¹ ∈ S := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [inv_zero]; exact S.zero_mem
    let m : S →ₗ[L] S :=
      { toFun := fun y => ⟨s * y, hmul' s hs y y.2⟩
        map_add' := fun y y' => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r y => Subtype.ext (by simp) }
    have hinj : Function.Injective m := fun y y' h =>
      Subtype.ext (mul_left_cancel₀ hs0 (congrArg Subtype.val h))
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨1, h1⟩
    have hy' : s * y = 1 := congrArg Subtype.val hy
    rw [inv_eq_of_mul_eq_one_right hy']
    exact y.2
  let S' : IntermediateField E M :=
    { carrier := S
      mul_mem' := fun ha hb => hmul' _ ha _ hb
      one_mem' := h1
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      algebraMap_mem' := fun c => by
        rw [IsScalarTower.algebraMap_apply E L M, Algebra.algebraMap_eq_smul_one]
        exact S.smul_mem _ h1
      inv_mem' := hinv }
  have hle : (⊤ : IntermediateField E M) ≤ S' := by
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr hT
  exact eq_top_iff.mpr fun y _ => hle (IntermediateField.mem_top (x := y))

end Span

section Setup

variable {K F E FE : Type*} [Field K] [Field F] [Algebra K F] [Field E] [Field FE]
  [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE]

theorem transcendental_algebraMap [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    {x : F} (hx : Transcendental K x) : Transcendental E (algebraMap F FE x) := by
  have hli : LinearIndependent K (fun n : ℕ => x ^ n) :=
    (linearIndependent_pow_iff_transcendental x).mpr hx
  have hli' := linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hli
  rw [← linearIndependent_pow_iff_transcendental]
  convert hli' using 1
  · funext n
    rw [map_pow]


variable (K F E FE) in
/-- The tensor-product map multiplying the images of the two fields in their common extension. -/
noncomputable def mulMap : E ⊗[K] F →ₐ[E] FE :=
  Algebra.TensorProduct.lift (Algebra.ofId E FE) (IsScalarTower.toAlgHom K F FE)
    (fun _ _ => Commute.all _ _)
@[scoped simp]
theorem mulMap_tmul (c : E) (f : F) :
    mulMap K F E FE (c ⊗ₜ f) = algebraMap E FE c * algebraMap F FE f := rfl

/-- The tensor-product evaluation map induced by the given base-field embedding. -/
noncomputable def evalMap (e : F →ₐ[K] E) : E ⊗[K] F →ₐ[E] E :=
  Algebra.TensorProduct.lift (AlgHom.id E E) e (fun _ _ => Commute.all _ _)
@[scoped simp]
theorem evalMap_tmul (e : F →ₐ[K] E) (c : E) (f : F) : evalMap e (c ⊗ₜ f) = c * e f := rfl

theorem mulMap_injective
    (hli : LinearIndependent E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i))) :
    Function.Injective (mulMap K F E FE) := by
  classical
  let bE := Algebra.TensorProduct.basis E (Module.Basis.ofVectorSpace K F)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hrepr : Finsupp.linearCombination E bE (bE.repr z) = z := bE.linearCombination_repr z
  have hcomp : ((mulMap K F E FE).toLinearMap : E ⊗[K] F →ₗ[E] FE) ∘ bE =
      fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F i) := by
    funext i
    simp [bE, Algebra.TensorProduct.basis_apply]
  have h0 : Finsupp.linearCombination E (fun i => algebraMap F FE (Module.Basis.ofVectorSpace K F
    i))
      (bE.repr z) = 0 := by
    rw [← hcomp, ← Finsupp.apply_linearCombination, hrepr]
    exact hz
  have hc : bE.repr z = 0 := hli (by rw [map_zero]; exact h0)
  rw [← hrepr, hc, map_zero]

theorem exists_centred [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) :
    ∃ P : Place E FE, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
  classical
  have hinj : Function.Injective (mulMap K F E FE) :=
    mulMap_injective (linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen
      (Module.Basis.ofVectorSpace K F).linearIndependent)
  let ε : (E ⊗[K] F) ≃ₐ[E] (mulMap K F E FE).range := AlgEquiv.ofInjective _ hinj
  let θ : (mulMap K F E FE).range →ₐ[E] E :=
    (evalMap e).comp (ε.symm : (mulMap K F E FE).range →ₐ[E] E ⊗[K] F)
  let I : Ideal (mulMap K F E FE).range := RingHom.ker θ.toRingHom
  have hI : I ≠ ⊤ := RingHom.ker_ne_top θ.toRingHom
  obtain ⟨B, hRB, hIB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := (mulMap K F E FE).range.toSubring) I hI
  have hEB : ∀ c : E, algebraMap E FE c ∈ B := fun c =>
    hRB ((mulMap K F E FE).range.algebraMap_mem c)
  have hval : ∀ f : F, mulMap K F E FE (1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f)) =
      algebraMap F FE f - algebraMap E FE (e f) := fun f => by
    rw [map_sub, AlgHom.commutes, mulMap_tmul, map_one, one_mul]
  have hmemR : ∀ f : F, algebraMap F FE f - algebraMap E FE (e f) ∈ (mulMap K F E FE).range :=
    fun f => (AlgHom.mem_range _).mpr ⟨_, hval f⟩
  have hcen : ∀ f : F, B.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1 := by
    intro f
    rw [← ValuationSubring.mem_nonunits_iff]
    refine hIB ⟨⟨_, hmemR f⟩, ?_, rfl⟩
    change θ ⟨_, hmemR f⟩ = 0
    have hsymm : ε.symm ⟨_, hmemR f⟩ = 1 ⊗ₜ f - algebraMap E (E ⊗[K] F) (e f) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      exact (hval f).symm
    change evalMap e (ε.symm ⟨_, hmemR f⟩) = 0
    rw [hsymm, map_sub, evalMap_tmul, one_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  obtain ⟨x, hx, -⟩ := id hfg
  have hxE : Transcendental E (algebraMap F FE x) := transcendental_algebraMap hfg hfgE hgen hx
  have htne : algebraMap F FE x - algebraMap E FE (e x) ≠ 0 := fun h =>
    hxE (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap (e x))
  have hBtop : B ≠ ⊤ := by
    intro hB
    have hmem := (ValuationSubring.mem_nonunits_iff (A := B)).mpr (hcen x)
    rcases (ValuationSubring.mem_nonunits_iff_or (A := B)).mp hmem with h0 | hinv
    · exact htne h0
    · exact hinv (hB ▸ ValuationSubring.mem_top _)
  obtain ⟨x₀, -, hx₀fin⟩ := id hfgE
  have := hx₀fin
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  obtain ⟨P, hP⟩ := Place.exists_of_valuationSubring (K := E) x₀ B hEB hBtop
  exact ⟨P, fun f => by rw [hP]; exact hcen f⟩

end Setup

end AlgebraicCurve.CentredPlaceRigidity

open AlgebraicCurve.CentredPlaceRigidity in
theorem _root_.AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (e : F →ₐ[K] E) (P Q : Place E FE)
    (hP : ∀ f : F, P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1)
    (hQ : ∀ f : F, Q.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (e f)) < 1) :
    P = Q := by
  classical
  obtain ⟨x, hx, hfin⟩ := id hfg
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx
  have : FiniteDimensional Kx F := hfin
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  have hxKx : x ∈ Kx := IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
  set x' : FE := algebraMap F FE x with hx'def
  have hx' : Transcendental E x' := transcendental_algebraMap hfg hfgE hgen hx
  set a : E := e x with hadef
  have ht0 : x' - algebraMap E FE a ≠ 0 := fun h =>
    hx' (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap a)
  let γ : RatFunc E ≃ₐ[E] E⟮x'⟯ := RatFunc.algEquivOfTranscendental x' hx'
  let ψ : RatFunc E →ₐ[E] FE := (IntermediateField.val _).comp (γ : RatFunc E →ₐ[E] E⟮x'⟯)
  let : Algebra (RatFunc E) FE := ψ.toRingHom.toAlgebra
  have : IsScalarTower E (RatFunc E) FE :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have hψ : ∀ r, algebraMap (RatFunc E) FE r = ψ r := fun r => rfl
  have hψX : algebraMap (RatFunc E) FE RatFunc.X = x' := by
    rw [hψ]
    exact RatFunc.algEquivOfTranscendental_X x' hx'
  have hψC : ∀ c : E, algebraMap (RatFunc E) FE (RatFunc.C c) = algebraMap E FE c := fun c => by
    have h : RatFunc.C c = algebraMap E (RatFunc E) c := by rw [RatFunc.algebraMap_eq_C]
    rw [h, ← IsScalarTower.algebraMap_apply]
  have hcoef : ∀ c : Kx, ∃ r : RatFunc E,
      algebraMap (RatFunc E) FE r = algebraMap F FE (c : F) := by
    intro c
    have hmem : algebraMap F FE (c : F) ∈ E⟮x'⟯ := by
      let φ : F →ₐ[K] FE := IsScalarTower.toAlgHom K F FE
      have h1 : φ (c : F) ∈ (IntermediateField.adjoin K ({x} : Set F)).map φ := ⟨c, c.2, rfl⟩
      rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
      have hle : IntermediateField.adjoin K ({φ x} : Set FE) ≤
          IntermediateField.restrictScalars K E⟮x'⟯ :=
        IntermediateField.adjoin_le_iff.mpr
          (Set.singleton_subset_iff.mpr (IntermediateField.mem_adjoin_simple_self E x'))
      exact hle h1
    refine ⟨γ.symm ⟨_, hmem⟩, ?_⟩
    rw [hψ]
    change ((γ (γ.symm ⟨_, hmem⟩) : E⟮x'⟯) : FE) = _
    rw [AlgEquiv.apply_symm_apply]
  set n : ℕ := Module.finrank Kx F with hndef
  let b := Module.finBasis Kx F
  let b' : Fin n → FE := fun i => algebraMap F FE (b i)
  have hT : ∀ f : F, algebraMap F FE f ∈ Submodule.span (RatFunc E) (Set.range b') := by
    intro f
    rw [← b.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hcoef (b.repr f i)
    rw [Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul, ← hr, ← Algebra.smul_def]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span (RatFunc E) (Set.range b') = ⊤ :=
    span_eq_top_of_adjoin_eq_top (E := E) b'
      (fun i j => by simpa only [b', ← map_mul] using hT (b i * b j))
      (by simpa only [map_one] using hT 1)
      (T := Set.range (algebraMap F FE)) (by rintro _ ⟨f, rfl⟩; exact hT f) hgen
  have : Module.Finite (RatFunc E) FE :=
    Module.finite_def.mpr (by rw [← hspan]; exact Submodule.fg_span (Set.finite_range b'))
  have hrank : Module.finrank (RatFunc E) FE ≤ n := by
    have h := finrank_range_le_card (R := RatFunc E) b'
    rw [Fintype.card_fin] at h
    change Module.finrank (RatFunc E) (Submodule.span (RatFunc E) (Set.range b')) ≤ n at h
    rwa [hspan, finrank_top] at h
  have : Algebra.IsIntegral (RatFunc E) FE := Algebra.IsIntegral.of_finite _ _
  have : CharZero (RatFunc E) :=
    charZero_of_injective_algebraMap (algebraMap E (RatFunc E)).injective
  have : Algebra.IsSeparable (RatFunc E) FE := Algebra.IsSeparable.of_integral _ _
  let v₀ : Place E (RatFunc E) := RationalFunctionField.placeOfPoint E a
  let Z : Finset (Place E FE) := v₀.fiber FE
  have hzero : ∀ P' : Place E FE,
      P'.toValuationSubring.valuation (x' - algebraMap E FE a) < 1 → P' ∈ Z := by
    intro P' hP'
    rw [Place.mem_fiber]
    rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty E (P'.restrict (RatFunc E)) with
      ⟨c, hc⟩ | hinf
    · rw [hc]
      by_contra hne
      have hca : c ≠ a := fun h => hne (by rw [h])
      have hordw : (RationalFunctionField.placeOfPoint E c).ord
          (RatFunc.X - RatFunc.C a : RatFunc E) = 0 := by
        have h := RationalFunctionField.ord_placeOfPoint_algebraMap c (Polynomial.X_sub_C_ne_zero a)
        rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C] at h
        rw [h, Polynomial.rootMultiplicity_X_sub_C, ite_eq_right hca, Nat.cast_zero]
      have hordP : P'.ord (x' - algebraMap E FE a) = 0 := by
        have h := P'.ord_restrict (RatFunc.X - RatFunc.C a : RatFunc E)
        rw [hc, hordw, mul_zero, map_sub, hψX, hψC] at h
        exact h
      exact ord_ne_zero_of_valuation_lt_one P' ht0 hP' hordP
    · exfalso
      have hxmem : x' ∈ P'.toValuationSubring := by
        have h := add_mem (mem_of_valuation_lt_one P' hP') (P'.algebraMap_mem' a)
        rwa [sub_add_cancel] at h
      have hX : (RatFunc.X : RatFunc E) ∈ (P'.restrict (RatFunc E)).toValuationSubring := by
        rw [Place.mem_restrict_iff, hψX]
        exact hxmem
      rw [hinf, RationalFunctionField.placeInfty_toValuationSubring,
        Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hX
      exact absurd hX (by norm_num)
  have hcardZ : Z.card ≤ n := by
    have hv₀ : v₀.IsRational := Place.isRational_of_isAlgClosed (K := E) v₀
    have hsum := Place.sum_ramificationIndex_eq_finrank (F' := FE) v₀ hv₀
      (fun w _ => Place.isRational_of_isAlgClosed (K := E) w)
    have h1 : (Z.card : ℤ) ≤ ∑ w ∈ Z, (w.ramificationIndex (RatFunc E) : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      rw [Nat.cast_one, Nat.one_le_cast]
      exact w.ramificationIndex_pos (F := RatFunc E)
    have h2 : (Z.card : ℤ) ≤ (n : ℤ) := by
      rw [hsum] at h1
      exact h1.trans (by exact_mod_cast hrank)
    exact_mod_cast h2
  let : Algebra Kx E := (e.comp Kx.val).toRingHom.toAlgebra
  have : IsScalarTower K Kx E :=
    IsScalarTower.of_algebraMap_eq fun c => ((e.comp Kx.val).commutes c).symm
  have : CharZero Kx := charZero_of_injective_algebraMap (algebraMap K Kx).injective
  have : Algebra.IsSeparable Kx F := Algebra.IsSeparable.of_integral _ _
  have hcardH : Fintype.card (F →ₐ[Kx] E) = n := AlgHom.card Kx F E
  have hHx : ∀ σ : F →ₐ[Kx] E, σ x = a := fun σ => by
    have h := σ.commutes ⟨x, hxKx⟩
    rw [IntermediateField.algebraMap_apply] at h
    exact h
  have hex : ∀ σ : F →ₐ[Kx] E, ∃ P' : Place E FE, ∀ f : F,
      P'.toValuationSubring.valuation
        (algebraMap F FE f - algebraMap E FE (σ.restrictScalars K f)) < 1 :=
    fun σ => exists_centred hfg hfgE hgen (σ.restrictScalars K)
  choose Pl hPl using hex
  have hPl_inj : Function.Injective Pl := fun σ τ h => by
    apply AlgHom.restrictScalars_injective K
    refine centre_unique (Pl σ) (hPl σ) ?_
    rw [h]
    exact hPl τ
  have hPlZ : ∀ σ, Pl σ ∈ Z := fun σ => hzero (Pl σ) (by
    have h := hPl σ x
    rwa [AlgHom.restrictScalars_apply, hHx σ] at h)
  have himg : Finset.univ.image Pl = Z := by
    apply Finset.eq_of_subset_of_card_le
    · intro P' hP'
      obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hP'
      exact hPlZ σ
    · rw [Finset.card_image_of_injective _ hPl_inj, Finset.card_univ, hcardH]
      exact hcardZ
  have hPZ : P ∈ Z := hzero P (hP x)
  have hQZ : Q ∈ Z := hzero Q (hQ x)
  rw [← himg] at hPZ hQZ
  obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hPZ
  obtain ⟨τ, -, hτ⟩ := Finset.mem_image.mp hQZ
  have hσe : σ.restrictScalars K = e := centre_unique P (by rw [← hσ]; exact hPl σ) hP
  have hτe : τ.restrictScalars K = e := centre_unique Q (by rw [← hτ]; exact hPl τ) hQ
  have hστ : σ = τ := AlgHom.restrictScalars_injective K (hσe.trans hτe.symm)
  rw [← hσ, ← hτ, hστ]
end AlgebraicCurves.Places.Proofs.Place_eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension
end ProofImplementation

attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
