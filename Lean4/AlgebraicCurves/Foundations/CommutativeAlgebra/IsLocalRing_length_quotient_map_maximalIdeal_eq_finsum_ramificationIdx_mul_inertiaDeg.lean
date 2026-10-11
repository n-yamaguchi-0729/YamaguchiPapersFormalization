/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Algebra.Module.LinearMap.End
import AlgebraicCurves.Valuations.IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring

/-!
# Is Local Ring length quotient map maximal Ideal eq finsum ramification Idx mul inertia Deg
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg

open IsLocalRing IsDedekindDomain

namespace NormLength

section Dict

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable {D₁ : Type*} [CommRing D₁] [IsDedekindDomain D₁] [Algebra C D₁]
variable {κ : Type*} [Field κ] [Algebra D₁ κ] [IsFractionRing D₁ κ] [Algebra C κ] [IsScalarTower C
  D₁ κ]

theorem isUnit_iff_inv_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : IsUnit x ↔ (x : L)⁻¹ ∈ B := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_left_inv
    have hyx : (y : L) * (x : L) = 1 := by
      have := congrArg (Subtype.val) hy
      simpa using this
    rw [← eq_inv_of_mul_eq_one_left hyx]
    exact y.2
  · exact isUnit_iff_exists_inv.mpr ⟨⟨_, hx⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

theorem mem_maximalIdeal_iff_inv_not_mem {L : Type*} [Field L] (B : ValuationSubring L) (x : B)
    (hx0 : (x : L) ≠ 0) : x ∈ maximalIdeal B ↔ (x : L)⁻¹ ∉ B := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff, isUnit_iff_inv_mem B x hx0]

theorem mem_nonunits_iff_eq_zero_or {L : Type*} [Field L] (B : ValuationSubring L) (x : L) :
    x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
  constructor
  · intro hx
    have hxB : x ∈ B := B.nonunits_le hx
    refine ⟨hxB, ?_⟩
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have : (⟨x, hxB⟩ : B) ∈ maximalIdeal B :=
        (ValuationSubring.coe_mem_nonunits_iff (a := ⟨x, hxB⟩)).mp hx
      exact (mem_maximalIdeal_iff_inv_not_mem B ⟨x, hxB⟩ hx0).mp this
  · rintro ⟨hxB, h⟩
    rw [show x = ((⟨x, hxB⟩ : B) : L) from rfl, ValuationSubring.coe_mem_nonunits_iff]
    rcases h with h | h
    · have : (⟨x, hxB⟩ : B) = 0 := Subtype.ext h
      rw [this]; exact Ideal.zero_mem _
    · exact (mem_maximalIdeal_iff_inv_not_mem B ⟨x, hxB⟩
        (fun h0 => h (by rw [show x = 0 from h0, inv_zero]; exact B.zero_mem))).mpr h

theorem inertiaDeg_maximalIdeal_eq_one_of_isLocalization {R : Type*} [CommRing R]
    (p : Ideal R) [p.IsMaximal] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    (maximalIdeal Rₚ).inertiaDeg R = 1 := by
  have : (maximalIdeal Rₚ).LiesOver p :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal Rₚ p).symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal p (maximalIdeal Rₚ)]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ
  have he : ∀ c, e c = algebraMap (R ⧸ p) (Rₚ ⧸ maximalIdeal Rₚ) c := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    rfl
  let e' : (R ⧸ p) ≃ₗ[R ⧸ p] (Rₚ ⧸ maximalIdeal Rₚ) :=
    { e with
      map_smul' := fun c x => by
        change e (c * x) = c • e x
        rw [map_mul, Algebra.smul_def, he] }
  rw [← e'.finrank_eq, Module.finrank_self]

variable (C D₁) in
/-- The condition that the valuation subring contains the two base rings and lies over the base
maximal ideal. -/
def Over (B : ValuationSubring κ) : Prop :=
  (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ x : D₁, algebraMap D₁ κ x ∈ B) ∧
    ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C

/-- The algebra structure on the valuation subring induced by the base-ring map landing in it. -/
abbrev overAlgebra (B : ValuationSubring κ) (h : ∀ c : C, algebraMap C κ c ∈ B) : Algebra C B :=
  ((algebraMap C κ).codRestrict B h).toAlgebra

/-- The product of the ramification index and inertia degree of the valuation subring over the
base. -/
noncomputable def ef (B : ValuationSubring κ) (h : ∀ c : C, algebraMap C κ c ∈ B) : ℕ :=
  letI := overAlgebra B h
  (maximalIdeal C).ramificationIdx' (maximalIdeal B) * (maximalIdeal B).inertiaDeg C
omit [IsDomain C] [IsDiscreteValuationRing C] [IsDedekindDomain D₁] in
theorem algebraMap_Cκ_injective : Function.Injective (algebraMap C κ) ↔
    Function.Injective (algebraMap C D₁) := by
  rw [IsScalarTower.algebraMap_eq C D₁ κ, RingHom.coe_comp]
  constructor
  · intro h; exact Function.Injective.of_comp h
  · intro h; exact (IsFractionRing.injective D₁ κ).comp h
omit [IsDedekindDomain D₁] in
theorem ne_top_of_over (hinj : Function.Injective (algebraMap C D₁))
    (B : ValuationSubring κ) (h : Over C D₁ B) : B ≠ ⊤ := by
  intro hB
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hϖ0 : algebraMap C κ ϖ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_Cκ_injective.mpr hinj)).mpr hϖ.ne_zero
  have hmem : algebraMap C κ ϖ ∈ B.nonunits := (h.2.2 ϖ).mpr hϖ.not_isUnit
  rcases ((mem_nonunits_iff_eq_zero_or B _).mp hmem).2 with h0 | hinv
  · exact hϖ0 h0
  · exact hinv (hB.symm ▸ ValuationSubring.mem_top _)

variable (C) in
theorem maximalIdeal_ne_bot : maximalIdeal C ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field C
omit [IsDiscreteValuationRing C] in
theorem isTorsionFree (hinj : Function.Injective (algebraMap C D₁)) : Module.IsTorsionFree C D₁ :=
  by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r c hrc
  rw [Algebra.smul_def] at hrc
  rcases mul_eq_zero.mp hrc with h | h
  · exact Or.inl (hinj (by rw [h, map_zero]))
  · exact Or.inr h

/-- The ring map to the valuation subring obtained by restricting the codomain of the field
inclusion. -/
noncomputable def toOver (B : ValuationSubring κ) (h : ∀ x : D₁, algebraMap D₁ κ x ∈ B) :
    D₁ →+* B :=
  (algebraMap D₁ κ).codRestrict B h
omit [IsDedekindDomain D₁] [IsFractionRing D₁ κ] in
@[scoped simp] theorem coe_toOver (B : ValuationSubring κ) (h : ∀ x : D₁, algebraMap D₁ κ x ∈ B)
    (s : D₁) : ((toOver B h s : B) : κ) = algebraMap D₁ κ s := rfl

/-- The center of the valuation subring on the intermediate ring. -/
noncomputable def center (B : ValuationSubring κ) (h : ∀ x : D₁, algebraMap D₁ κ x ∈ B) :
    Ideal D₁ :=
  (maximalIdeal B).comap (toOver B h)
omit [IsDedekindDomain D₁] [IsFractionRing D₁ κ] in
theorem mem_center_iff (B : ValuationSubring κ) (h : ∀ x : D₁, algebraMap D₁ κ x ∈ B)
    (s : D₁) : s ∈ center B h ↔ algebraMap D₁ κ s ∈ B.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

scoped instance center_isPrime (B : ValuationSubring κ) (h : ∀ x : D₁, algebraMap D₁ κ x ∈ B) :
    (center B h).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain D₁] [IsFractionRing D₁ κ] in
theorem comap_center (B : ValuationSubring κ) (h : Over C D₁ B) :
    (center B h.2.1).comap (algebraMap C D₁) = maximalIdeal C := by
  ext c
  rw [Ideal.mem_comap, mem_center_iff, ← IsScalarTower.algebraMap_apply, h.2.2]

scoped instance center_liesOver (B : ValuationSubring κ) (h : Over C D₁ B) :
    (center B h.2.1).LiesOver (maximalIdeal C) :=
  ⟨(comap_center B h).symm⟩

omit [IsDedekindDomain D₁] [IsFractionRing D₁ κ] in
theorem center_ne_bot (hinj : Function.Injective (algebraMap C D₁)) (B : ValuationSubring κ)
    (h : Over C D₁ B) : center B h.2.1 ≠ ⊥ := by
  intro h0
  have h1 : (center B h.2.1).comap (algebraMap C D₁) = ⊥ := by
    rw [h0, Ideal.comap_bot_of_injective _ hinj]
  rw [comap_center B h] at h1
  exact maximalIdeal_ne_bot C h1

/-- The height-one prime determined by the center of the valuation subring. -/
noncomputable def vOf (hinj : Function.Injective (algebraMap C D₁)) (B : ValuationSubring κ)
    (h : Over C D₁ B) : HeightOneSpectrum D₁ :=
  ⟨center B h.2.1, inferInstance, center_ne_bot hinj B h⟩

/-- The valuation subring associated with a height-one prime of the intermediate ring. -/
noncomputable abbrev W (v : HeightOneSpectrum D₁) : ValuationSubring κ :=
  HeightOneSpectrum.valuationSubringAtPrime κ v

theorem isDiscreteValuationRing_W (v : HeightOneSpectrum D₁) : IsDiscreteValuationRing (W (κ := κ)
  v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D₁ v.ne_bot (W v)

theorem coe_algebraMap_W (v : HeightOneSpectrum D₁) (s : D₁) :
    ((algebraMap D₁ (W (κ := κ) v) s : W v) : κ) = algebraMap D₁ κ s := rfl

variable (C) in
theorem over_W (v : HeightOneSpectrum D₁) [v.asIdeal.LiesOver (maximalIdeal C)] :
    Over C D₁ (W (κ := κ) v) := by
  have key : ∀ c : C, algebraMap C κ c =
      ((algebraMap D₁ (W (κ := κ) v) (algebraMap C D₁ c) : W v) : κ) :=
    fun c => IsScalarTower.algebraMap_apply C D₁ κ c
  refine ⟨fun c => ?_, fun x => ?_, fun c => ?_⟩
  · rw [key]; exact SetLike.coe_mem _
  · rw [← coe_algebraMap_W v x]; exact SetLike.coe_mem _
  · rw [key, ValuationSubring.coe_mem_nonunits_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (W v) v.asIdeal,
      Ideal.over_def v.asIdeal (maximalIdeal C), Ideal.under_def, Ideal.mem_comap]

theorem W_vOf_le (hinj : Function.Injective (algebraMap C D₁)) (B : ValuationSubring κ)
    (h : Over C D₁ B) : W (vOf hinj B h) ≤ B := by
  rintro y ⟨a, s, hs, rfl⟩
  refine B.mul_mem _ _ (h.2.1 a) ?_
  have hs' : s ∉ center B h.2.1 := hs
  have hs0 : algebraMap D₁ κ s ≠ 0 := by
    rintro h0
    apply hs'
    have : s = 0 := (IsFractionRing.injective D₁ κ) (by rw [h0, map_zero])
    rw [this]; exact Ideal.zero_mem _
  have := (mem_maximalIdeal_iff_inv_not_mem B (toOver B h.2.1 s) hs0).not.mp
    (fun hm => hs' (Ideal.mem_comap.mpr hm))
  simpa using this

theorem W_vOf_eq (hinj : Function.Injective (algebraMap C D₁)) (B : ValuationSubring κ)
    (h : Over C D₁ B) : W (vOf hinj B h) = B :=
  ValuationSubring.eq_of_le_of_ne_top _ (W_vOf_le hinj B h) (ne_top_of_over hinj B h)

theorem vOf_W (hinj : Function.Injective (algebraMap C D₁)) (v : HeightOneSpectrum D₁)
    [v.asIdeal.LiesOver (maximalIdeal C)] : vOf hinj (W (κ := κ) v) (over_W C v) = v := by
  apply HeightOneSpectrum.ext
  ext s
  change s ∈ center (W v) (over_W C v).2.1 ↔ s ∈ v.asIdeal
  rw [mem_center_iff, ← coe_algebraMap_W v s, ValuationSubring.coe_mem_nonunits_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (W v) v.asIdeal]

theorem ef_W (hinj : Function.Injective (algebraMap C D₁)) (v : HeightOneSpectrum D₁)
    [v.asIdeal.LiesOver (maximalIdeal C)] :
    ef (W (κ := κ) v) (over_W C v).1 =
    (maximalIdeal C).ramificationIdx' v.asIdeal * v.asIdeal.inertiaDeg C := by
  let : Algebra C (W (κ := κ) v) := overAlgebra (W v) (over_W C v).1
  have : IsScalarTower C D₁ (W (κ := κ) v) :=
    IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (IsScalarTower.algebraMap_apply C D₁ κ c)
  have : IsDiscreteValuationRing (W (κ := κ) v) := isDiscreteValuationRing_W v
  have hmapS : Ideal.map (algebraMap D₁ (W (κ := κ) v)) v.asIdeal = maximalIdeal (W v) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (W v)
  have hmW0 : maximalIdeal (W (κ := κ) v) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have : (maximalIdeal (W (κ := κ) v)).LiesOver v.asIdeal :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal (W v) v.asIdeal).symm⟩
  have hinj' : Function.Injective (algebraMap C (W (κ := κ) v)) := by
    intro a b hab
    have h' : algebraMap C κ a = algebraMap C κ b := congrArg (fun z : W (κ := κ) v => (z : κ)) hab
    exact (algebraMap_Cκ_injective.mpr hinj) h'
  have he : (maximalIdeal C).ramificationIdx' (maximalIdeal (W (κ := κ) v)) =
      (maximalIdeal C).ramificationIdx' v.asIdeal *
        v.asIdeal.ramificationIdx' (maximalIdeal (W (κ := κ) v)) :=
    Ideal.ramificationIdx'_algebra_tower (by rw [hmapS]; exact hmW0)
      (by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj']
        exact maximalIdeal_ne_bot C)
      hmapS.le
  have he1 : v.asIdeal.ramificationIdx' (maximalIdeal (W (κ := κ) v)) = 1 := by
    rw [← hmapS]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmapS]; exact (maximalIdeal.isMaximal _).ne_top) (by rw [hmapS]; exact hmW0)
  have hf : (maximalIdeal (W (κ := κ) v)).inertiaDeg C =
      v.asIdeal.inertiaDeg C * (maximalIdeal (W (κ := κ) v)).inertiaDeg D₁ :=
    Ideal.inertiaDeg_tower (R := C) v.asIdeal (maximalIdeal (W (κ := κ) v))
  have hf1 : (maximalIdeal (W (κ := κ) v)).inertiaDeg D₁ = 1 :=
    inertiaDeg_maximalIdeal_eq_one_of_isLocalization v.asIdeal (W v)
  change (maximalIdeal C).ramificationIdx' (maximalIdeal (W (κ := κ) v)) *
      (maximalIdeal (W (κ := κ) v)).inertiaDeg C = _
  rw [he, he1, hf, hf1, mul_one, mul_one]

end Dict

theorem valuationSubring_equiv_primesOver
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D₁ : Type*} [CommRing D₁] [IsDedekindDomain D₁] [Algebra C D₁]
    (κ : Type*) [Field κ] [Algebra D₁ κ] [IsFractionRing D₁ κ] [Algebra C κ] [IsScalarTower C D₁ κ]
    [Algebra K κ] [IsScalarTower C K κ]
    (hinj : Function.Injective (algebraMap C D₁)) :
    ∃ ε : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ x : D₁, algebraMap D₁ κ x
      ∈ B) ∧
              ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C}
            ≃ ↥(IsDedekindDomain.primesOverFinset (maximalIdeal C) D₁),
      ∀ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧
          (∀ x : D₁, algebraMap D₁ κ x ∈ B) ∧ ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈
            maximalIdeal C},
        (letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
         (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) *
           (maximalIdeal ↥B.1).inertiaDeg C) =
          (maximalIdeal C).ramificationIdx' (ε B).1 * (ε B).1.inertiaDeg C := by
  classical
  have : Module.IsTorsionFree C D₁ := isTorsionFree hinj
  have hmem : ∀ P : Ideal D₁, P ∈ IsDedekindDomain.primesOverFinset (maximalIdeal C) D₁ ↔
      P.IsPrime ∧ P.LiesOver (maximalIdeal C) := fun P =>
    IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot C) D₁
  let hos : ↥(IsDedekindDomain.primesOverFinset (maximalIdeal C) D₁) → HeightOneSpectrum D₁ := fun
    P =>
    haveI := ((hmem P.1).mp P.2).1
    haveI := ((hmem P.1).mp P.2).2
    ⟨P.1, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot (maximalIdeal_ne_bot C) P.1⟩
  have hos_over : ∀ P : ↥(IsDedekindDomain.primesOverFinset (maximalIdeal C) D₁),
      (hos P).asIdeal.LiesOver (maximalIdeal C) := fun P => ((hmem P.1).mp P.2).2
  let ε : {B : ValuationSubring κ // Over C D₁ B} ≃ ↥(IsDedekindDomain.primesOverFinset
    (maximalIdeal C) D₁) :=
    { toFun := fun B => ⟨center B.1 B.2.2.1, (hmem _).mpr ⟨inferInstance, center_liesOver B.1 B.2⟩⟩
      invFun := fun P => haveI := hos_over P; ⟨W (hos P), over_W C (hos P)⟩
      left_inv := fun B => Subtype.ext (W_vOf_eq hinj B.1 B.2)
      right_inv := fun P => by
        have := hos_over P
        exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal (vOf_W (κ := κ) hinj (hos P))) }
  refine ⟨ε, fun B => ?_⟩
  have := hos_over (ε B)
  have key : B = ε.symm (ε B) := (ε.symm_apply_apply B).symm
  have : (letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) *
            (maximalIdeal ↥B.1).inertiaDeg C) = ef B.1 B.2.1 := rfl
  rw [this]
  conv_lhs => rw [key]
  exact ef_W hinj (hos (ε B))

section CRT

/-
The finite-fiber sum argument below is adapted from Mathlib by Thomas Browning:
Copyright (c) 2026 Thomas Browning. All rights reserved.
The primes-over argument is adapted from Mathlib by Kenji Nakagawa,
Anne Baanen, and Filippo A. E. Nuccio:
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Both sources are released under Apache 2.0 as described in LICENSE.
Pinned sources:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/RamificationInertia/Basic.lean
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean
The quotient/fiber bridge and local adaptation are by Naganori Yamaguchi
(assisted by OpenAI Codex), https://github.com/n-yamaguchi-0729.
-/

open IsLocalRing Module OrderIso PrimeSpectrum

theorem sum_ramification_inertia_eq_finrank_finite_fiber
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite p.ResidueField (p.Fiber S)] [Fintype (p.primesOver S)] :
    ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R =
      finrank p.ResidueField (p.Fiber S) := by
  classical
  let : IsArtinianRing (p.Fiber S) := IsArtinianRing.of_finite p.ResidueField (p.Fiber S)
  let := Fintype.ofFinite (PrimeSpectrum (p.Fiber S))
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum, ← (primesOverOrderIsoFiber R S p).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro q _
  simp_rw [toEquiv_symm, coe_symm_toEquiv, coe_primesOverOrderIsoFiber_symm_apply]
  set r := q.1.comap Algebra.TensorProduct.includeRight
  let := Localization.AtPrime.algebraOfLiesOver p r
  rw [Ideal.ramificationIdx_eq p r, Ideal.inertiaDeg_eq p r]
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q.1
  let Sr := Localization.AtPrime r
  let κp := p.ResidueField
  let κr := r.ResidueField
  let A := Sr ⧸ p.map (algebraMap R Sr)
  have : Module.Finite κp Sq :=
    Module.Finite.of_surjective (Algebra.algHom κp (p.Fiber S) Sq).toLinearMap
      (IsArtinianRing.localization_surjective q.1.primeCompl Sq)
  have : (maximalIdeal Sr).LiesOver r :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal Sr r).symm⟩
  have : (maximalIdeal Sr).LiesOver p := Ideal.LiesOver.trans (maximalIdeal Sr) r p
  have hle : p.map (algebraMap R Sr) ≤ maximalIdeal Sr := by
    rw [Ideal.map_le_iff_le_comap]
    exact (Ideal.over_def (maximalIdeal Sr) p).le
  let f : A →ₐ[Rp] κr := Ideal.Quotient.liftₐ _ (IsScalarTower.toAlgHom Rp Sr κr)
    (fun x hx => (IsLocalRing.residue_eq_zero_iff x).mpr (hle hx))
  have hf : Function.Surjective f :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ IsLocalRing.residue_surjective
  let g : Sq →ₐ[κp] κr :=
    (f.comp (Ideal.Fiber.localizationAlgEquivQuotient p q.1).toAlgHom).extendScalarsOfSurjective
      (IsLocalRing.residue_surjective (R := Rp))
  have : Module.Finite κp κr := Module.Finite.of_surjective g.toLinearMap
    (hf.comp (Ideal.Fiber.localizationAlgEquivQuotient p q.1).surjective)
  suffices length Sr A * finrank κp κr = finrank κp Sq by simpa using congr_arg ENat.toNat this
  calc length Sr A * finrank κp κr = length Sr A * length κp κr := by rw [length_eq_finrank]
    _ = length Rp A := (length_restrictScalars Rp Sr A).symm
    _ = length Rp Sq := (Ideal.Fiber.localizationAlgEquivQuotient p
      q.1).toLinearEquiv.length_eq.symm
    _ = length κp Sq := length_eq_of_surjective residue_surjective
    _ = finrank κp Sq := length_eq_finrank κp Sq



attribute [local instance] Ideal.Quotient.field

/-- The algebra equivalence between quotient by the extended maximal ideal and the corresponding
fiber. -/
noncomputable def quotientFiberAlgEquiv
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (S : Type*) [CommRing S] [Algebra R S] :
    (S ⧸ p.map (algebraMap R S)) ≃ₐ[R ⧸ p] p.Fiber S :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p).trans
    (Algebra.TensorProduct.congr
      (IsFractionRing.algEquiv (R ⧸ p) (R ⧸ p) p.ResidueField) (AlgEquiv.refl))

theorem finite_fiber_and_finrank_eq_quotient
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite (R ⧸ p) (S ⧸ p.map (algebraMap R S))] :
    Module.Finite p.ResidueField (p.Fiber S) ∧
      Module.finrank p.ResidueField (p.Fiber S) =
        Module.finrank (R ⧸ p) (S ⧸ p.map (algebraMap R S)) := by
  let e := quotientFiberAlgEquiv p S
  have : Module.Finite (R ⧸ p) (p.Fiber S) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  refine ⟨Module.Finite.of_restrictScalars_finite (R ⧸ p) p.ResidueField (p.Fiber S), ?_⟩
  let i := IsFractionRing.algEquiv (R ⧸ p) (R ⧸ p) p.ResidueField
  symm
  apply Algebra.finrank_eq_of_equiv_equiv i.toRingEquiv e.toRingEquiv
  ext x
  change algebraMap p.ResidueField (p.Fiber S) (i x) = e (algebraMap (R ⧸ p) _ x)
  rw [e.commutes]
  rw [show i x = algebraMap (R ⧸ p) p.ResidueField x from i.commutes x]
  exact (IsScalarTower.algebraMap_apply (R ⧸ p) p.ResidueField (p.Fiber S) x).symm



open Ideal UniqueFactorizationMonoid
variable {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
theorem mem_primesOver_iff_mem_factors_of_map_ne_bot (p : Ideal R) [h : p.IsMaximal]
    (hp : p.map (algebraMap R S) ≠ ⊥) {P : Ideal S} :
    P ∈ p.primesOver S ↔ P ∈ normalizedFactors (p.map (algebraMap R S)) := by
  rw [primesOver, Set.mem_ofPred_eq, Ideal.mem_normalizedFactors_iff hp,
    liesOver_iff, under_def, and_congr_right_iff, map_le_iff_le_comap]
  intro hP
  refine ⟨fun h ↦ le_of_eq h, fun h' ↦ ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩
  exact comap_ne_top (algebraMap R S) (IsPrime.ne_top hP)
theorem coe_primesOverFinset_of_map_ne_bot (p : Ideal R) [p.IsMaximal]
    (hp : p.map (algebraMap R S) ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p S : Set (Ideal S)) = p.primesOver S := by
  ext P
  simpa using (mem_primesOver_iff_mem_factors_of_map_ne_bot p hp (P := P)).symm

theorem finrank_quotient_map_eq_sum
    {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]
    (p : Ideal R) [p.IsMaximal] (hp : p.map (algebraMap R S) ≠ ⊥)
    [Module.Finite (R ⧸ p) (S ⧸ p.map (algebraMap R S))] :
    Module.finrank (R ⧸ p) (S ⧸ p.map (algebraMap R S)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p S,
        p.ramificationIdx' P * P.inertiaDeg R := by
  classical
  let e : (IsDedekindDomain.primesOverFinset p S : Set (Ideal S)) ≃ p.primesOver S :=
    Set.equivOfEq (coe_primesOverFinset_of_map_ne_bot p hp)
  let : Fintype (p.primesOver S) := Fintype.ofEquiv _ e
  obtain ⟨hfinite, hfinrank⟩ := finite_fiber_and_finrank_eq_quotient p S
  rw [← hfinrank, ← sum_ramification_inertia_eq_finrank_finite_fiber p S]
  rw [← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset p S)]
  symm
  apply Fintype.sum_equiv e
  intro P
  have : P.1.IsPrime := (e P).2.1
  have : P.1.LiesOver p := (e P).2.2
  change p.ramificationIdx' P.1 * P.1.inertiaDeg R = P.1.ramificationIdx R * P.1.inertiaDeg R
  rw [Ideal.ramificationIdx'_eq_ramificationIdx' p P.1 hp]

end CRT

theorem finrank_quotient_map_maximalIdeal_eq_finsum
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D₁ : Type*} [CommRing D₁] [IsDedekindDomain D₁] [Algebra C D₁]
    (κ : Type*) [Field κ] [Algebra D₁ κ] [IsFractionRing D₁ κ] [Algebra C κ] [IsScalarTower C D₁ κ]
    [Algebra K κ] [IsScalarTower C K κ]
    (hinj : Function.Injective (algebraMap C D₁))
    [Module.Finite (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁))] :
    Finite {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ x : D₁, algebraMap D₁ κ
      x ∈ B) ∧
        ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C} ∧
    (Module.finrank (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) : ℕ∞) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ x : D₁, algebraMap D₁
        κ x ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal ↥B.1).inertiaDeg C
            : ℕ) : ℕ∞) := by
  classical
  obtain ⟨ε, hε⟩ := valuationSubring_equiv_primesOver K κ hinj (D₁ := D₁)
  have : Fintype {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧
      (∀ x : D₁, algebraMap D₁ κ x ∈ B) ∧ ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal
        C} :=
    Fintype.ofEquiv _ ε.symm
  refine ⟨Finite.of_fintype _, ?_⟩
  have hp : Ideal.map (algebraMap C D₁) (maximalIdeal C) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact maximalIdeal_ne_bot C
  rw [finsum_eq_sum_of_fintype, ← Nat.cast_sum, finrank_quotient_map_eq_sum (maximalIdeal C) hp,
    Fintype.sum_equiv ε _
      (fun P => (maximalIdeal C).ramificationIdx' P.1 * P.1.inertiaDeg C) hε,
    Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset (maximalIdeal C) D₁)
      (fun P => (maximalIdeal C).ramificationIdx' P * P.inertiaDeg C)]

section Overring

variable {D : Type*} [CommRing D] [IsDomain D] (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing
  D κ]

theorem isFractionRing_subalgebra (D₁ : Subalgebra D κ) : IsFractionRing ↥D₁ κ := by
  have : FaithfulSMul ↥D₁ κ := (faithfulSMul_iff_algebraMap_injective ↥D₁ κ).mpr
    Subtype.coe_injective
  refine IsFractionRing.of_field (R := ↥D₁) (K := κ) (fun z => ?_)
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors D) z
  refine ⟨⟨algebraMap D κ a, Subalgebra.algebraMap_mem D₁ a⟩, ⟨algebraMap D κ s,
    Subalgebra.algebraMap_mem D₁ s⟩, ?_⟩
  have hs : algebraMap D κ (s : D) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective D κ)).mpr (nonZeroDivisors.ne_zero s.2)
  change z = algebraMap D κ a / algebraMap D κ s
  rw [eq_div_iff hs]
  simpa using h

variable {κ}

theorem isDedekindDomain_of_locallyPrincipal [IsNoetherianRing D] [IsLocalRing D] (hDdim :
  Ring.DimensionLEOne D)
    (D₁ : Subalgebra D κ) (hfin : Module.Finite D ↥D₁)
    (hloc : ∀ 𝔫 : Ideal ↥D₁, 𝔫.IsMaximal → ∃ t ∈ 𝔫, ∀ x ∈ 𝔫, ∃ s ∉ 𝔫, ∃ y : ↥D₁, s * x = t * y) :
    IsDedekindDomain ↥D₁ := by
  have := hfin
  have := hDdim
  have : IsNoetherianRing ↥D₁ := isNoetherian_of_tower D
    (isNoetherian_of_isNoetherianRing_of_finite D ↥D₁)
  have : Algebra.IsIntegral D ↥D₁ := Algebra.IsIntegral.of_finite D ↥D₁
  have : Ring.DimensionLEOne ↥D₁ := Ring.DimensionLEOne.of_isIntegral D ↥D₁
  have := isFractionRing_subalgebra κ D₁
  have hic : IsIntegrallyClosed ↥D₁ := by
    refine IsIntegrallyClosed.of_localization_maximal fun p hp0 hpmax => ?_
    have := hpmax
    obtain ⟨t, ht, hgen⟩ := hloc p hpmax
    have hprinc : (maximalIdeal (Localization.AtPrime p)).IsPrincipal := by
      refine ⟨algebraMap ↥D₁ (Localization.AtPrime p) t, le_antisymm ?_ ?_⟩
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
          Ideal.map_le_iff_le_comap]
        intro x hx
        obtain ⟨s, hs, y, hsy⟩ := hgen x hx
        rw [Ideal.mem_comap, Ideal.submodule_span_eq, Ideal.mem_span_singleton']
        have hsu : IsUnit (algebraMap ↥D₁ (Localization.AtPrime p) s) :=
          IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
        refine ⟨hsu.unit⁻¹ * algebraMap ↥D₁ (Localization.AtPrime p) y, ?_⟩
        rw [mul_assoc, mul_comm _ (algebraMap _ _ t), ← map_mul, ← hsy, map_mul, ← mul_assoc,
          IsUnit.val_inv_mul, one_mul]
      · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
        exact Ideal.mem_map_of_mem _ ht
    have hnf : ¬ IsField (Localization.AtPrime p) := by
      intro hf
      have := (IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p))
      rw [IsLocalRing.isField_iff_maximalIdeal_eq] at hf
      rw [hf, Ideal.map_eq_bot_iff_of_injective] at this
      · exact hp0 this
      · exact IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
    have : IsDiscreteValuationRing (Localization.AtPrime p) :=
      ((IsDiscreteValuationRing.TFAE (Localization.AtPrime p) hnf).out 5 1).mp hprinc
    infer_instance
  exact (isDedekindDomain_iff ↥D₁ κ).mpr ⟨inferInstance, inferInstance, inferInstance,
    fun {x} hx => (isIntegrallyClosed_iff κ).mp hic hx⟩

end Overring

section FiniteLength

variable {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D]

omit [IsDomain D] in
theorem isArtinianRing_quotient_of_ne_bot (hDdim : Ring.DimensionLEOne D) (𝔟 : Ideal D) (h𝔟 : 𝔟 ≠
  ⊥) :
    IsArtinianRing (D ⧸ 𝔟) := by
  have := hDdim
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  refine ⟨inferInstance, Ring.KrullDimLE.mk₀ fun P hP => ?_⟩
  have := hP
  have hPc : (P.comap (Ideal.Quotient.mk 𝔟)).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime (fun h => h𝔟 ?_) (Ideal.IsPrime.comap _)
    refine le_bot_iff.mp fun x hx => ?_
    rw [← h, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.zero_mem
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔟)
    Ideal.Quotient.mk_surjective hPc
    with h | h
  · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact absurd h hP.ne_top
  · rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h
omit [IsDomain D] in
theorem length_ne_top_of_smul_eq_zero (hDdim : Ring.DimensionLEOne D)
    {M : Type*} [AddCommGroup M] [Module D M] [Module.Finite D M]
    (d : D) (hd : d ≠ 0) (hM : ∀ m : M, d • m = 0) : Module.length D M ≠ ⊤ := by
  classical
  set 𝔟 : Ideal D := Ideal.span {d} with h𝔟
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rw [h𝔟, Ne, Ideal.span_singleton_eq_bot]; exact hd
  have htors : Module.IsTorsionBySet D M (𝔟 : Set D) := by
    intro m ⟨a, ha⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    change (c * d) • m = 0
    rw [mul_smul, hM, smul_zero]
  let : Module (D ⧸ 𝔟) M := htors.module
  have : IsScalarTower D (D ⧸ 𝔟) M := Module.IsTorsionBySet.isScalarTower htors (S := D)
  have : IsArtinianRing (D ⧸ 𝔟) := isArtinianRing_quotient_of_ne_bot hDdim 𝔟 h𝔟0
  have : Module.Finite (D ⧸ 𝔟) M := Module.Finite.of_restrictScalars_finite D (D ⧸ 𝔟) M
  have : IsArtinian (D ⧸ 𝔟) M := isArtinian_of_fg_of_artinian'
  have : IsNoetherian (D ⧸ 𝔟) M := isNoetherian_of_isNoetherianRing_of_finite (D ⧸ 𝔟) M
  rw [Module.length_eq_of_surjective (S := D) (R := D ⧸ 𝔟) (M := M) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

end FiniteLength

section Lattice

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

open Pointwise in
theorem length_quotient_span_singleton_smul_top_eq (x : R) (hx : ∀ m : M, x • m = 0 → m = 0)
    (N : Submodule R M) (hN : Module.length R (M ⧸ N) ≠ ⊤) :
    Module.length R (↥N ⧸ ((Ideal.span {x} : Ideal R) • (⊤ : Submodule R ↥N))) =
      Module.length R (M ⧸ ((Ideal.span {x} : Ideal R) • (⊤ : Submodule R M))) := by
  set xN : Submodule R M := (Ideal.span {x} : Ideal R) • N with hxN
  set xM : Submodule R M := (Ideal.span {x} : Ideal R) • (⊤ : Submodule R M) with hxM
  have hmem_xN : ∀ m : M, m ∈ xN ↔ ∃ n ∈ N, m = x • n := fun m => by
    rw [hxN, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨n, hn, h⟩ => ⟨n, hn, h.symm⟩, fun ⟨n, hn, h⟩ => ⟨n, hn, h.symm⟩⟩
  have hmem_xM : ∀ m : M, m ∈ xM ↔ ∃ n : M, m = x • n := fun m => by
    rw [hxM, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨n, _, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, Submodule.mem_top, h.symm⟩⟩
  have hxN_le_N : xN ≤ N := by rw [hxN]; exact Submodule.smul_le_right
  have hxN_le_xM : xN ≤ xM := by rw [hxN, hxM]; exact Submodule.smul_mono le_rfl le_top
  let f₁ : ↥N →ₗ[R] M ⧸ xN := xN.mkQ.comp N.subtype
  have hf₁_range : LinearMap.range f₁ = N.map xN.mkQ := by
    change LinearMap.range (xN.mkQ.comp N.subtype) = N.map xN.mkQ
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hf₁_ker : LinearMap.ker f₁ = (Ideal.span {x} : Ideal R) • (⊤ : Submodule R ↥N) := by
    ext n
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hmem_xN,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨m, hm, h⟩
      exact ⟨⟨m, hm⟩, Submodule.mem_top, Subtype.ext (by simpa using h.symm)⟩
    · rintro ⟨m, -, h⟩
      exact ⟨m, m.2, by rw [← h]; rfl⟩
  have e₁ : (↥N ⧸ ((Ideal.span {x} : Ideal R) • (⊤ : Submodule R ↥N))) ≃ₗ[R] ↥(N.map xN.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hf₁_ker.symm).trans ((LinearMap.quotKerEquivRange f₁).trans
      (LinearEquiv.ofEq _ _ hf₁_range))
  have h₁ : Module.length R (M ⧸ xN) = Module.length R ↥(N.map xN.mkQ) + Module.length R (M ⧸ N) :=
    by
    rw [← (Submodule.quotientQuotientEquivQuotient xN N hxN_le_N).length_eq]
    exact Module.length_eq_add_of_exact (N.map xN.mkQ).subtype (N.map xN.mkQ).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  let f₂ : M →ₗ[R] M ⧸ xN := xN.mkQ.comp (DistribSMul.toLinearMap R M x)
  have hf₂_range : LinearMap.range f₂ = xM.map xN.mkQ := by
    rw [LinearMap.range_comp]
    congr 1
    ext m
    rw [LinearMap.mem_range, hmem_xM]
    exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩
  have hf₂_ker : LinearMap.ker f₂ = N := by
    ext m
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, hmem_xN]
    constructor
    · rintro ⟨n, hn, h⟩
      have : m = n := by
        have h' : x • (m - n) = 0 := by rw [smul_sub, sub_eq_zero]; exact h
        exact sub_eq_zero.mp (hx _ h')
      rw [this]; exact hn
    · intro hm
      exact ⟨m, hm, rfl⟩
  have e₂ : (M ⧸ N) ≃ₗ[R] ↥(xM.map xN.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hf₂_ker.symm).trans ((LinearMap.quotKerEquivRange f₂).trans
      (LinearEquiv.ofEq _ _ hf₂_range))
  have h₂ : Module.length R (M ⧸ xN) = Module.length R ↥(xM.map xN.mkQ) + Module.length R (M ⧸ xM)
    := by
    rw [← (Submodule.quotientQuotientEquivQuotient xN xM hxN_le_xM).length_eq]
    exact Module.length_eq_add_of_exact (xM.map xN.mkQ).subtype (xM.map xN.mkQ).mkQ
      (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [e₁.length_eq, ← e₂.length_eq] at *
  rw [h₁, add_comm] at h₂
  exact (ENat.add_right_injective_of_ne_top hN) h₂

end Lattice

section LengthTransfer

open IsLocalRing

variable {A R : Type*} [CommRing A] [CommRing R] [IsLocalRing R] [Algebra A R]

theorem IsSimpleModule.of_surjective_residue_comp_algebraMap
    (h : Function.Surjective ((residue R).comp (algebraMap A R)))
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [IsSimpleModule R
      M] :
    IsSimpleModule A M := by
  have hann : Module.annihilator R M = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := R) (M := M))
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨IsSimpleModule.nontrivial R M, fun x hx z => ?_⟩
  obtain ⟨r, rfl⟩ := IsSimpleModule.toSpanSingleton_surjective R hx z
  obtain ⟨a, ha⟩ := h (residue R r)
  refine ⟨a, ?_⟩
  simp only [LinearMap.toSpanSingleton_apply]
  have hmem : r - algebraMap A R a ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact ha.symm
  rw [← hann, Module.mem_annihilator] at hmem
  have := hmem x
  rw [sub_smul, sub_eq_zero] at this
  rw [this, algebraMap_smul]

theorem Module.length_restrictScalars_eq_of_surjective_residue_aux
    (h : Function.Surjective ((residue R).comp (algebraMap A R))) :
    ∀ (M : Type*) [AddCommGroup M] [Module R M], IsFiniteLength R M →
      ∀ [Module A M] [IsScalarTower A R M], Module.length A M = Module.length R M := by
  intro M _ _ hM
  induction hM with
  | of_subsingleton => intro _ _; rw [Module.length_eq_zero, Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimp hN ih =>
    intro _ _
    have hR := Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
      (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    have hA := Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
      (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
    have : IsSimpleModule A (M ⧸ N) := IsSimpleModule.of_surjective_residue_comp_algebraMap h (M ⧸
      N)
    rw [hR, hA, ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one R (M ⧸ N)]

theorem Module.length_restrictScalars_eq_of_surjective_residue
    (h : Function.Surjective ((residue R).comp (algebraMap A R)))
    {M : Type*} [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M)
    [Module A M] [IsScalarTower A R M] :
    Module.length A M = Module.length R M :=
  Module.length_restrictScalars_eq_of_surjective_residue_aux h M hM

end LengthTransfer

theorem core
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (_hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (_hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ]
    (D₁ : Type*) [CommRing D₁] [IsDedekindDomain D₁] [Algebra D D₁] [Module.Finite D D₁]
    [Algebra C D₁] [IsScalarTower C D D₁] [Algebra D₁ κ] [IsFractionRing D₁ κ]
    [IsScalarTower D D₁ κ] [IsScalarTower C D₁ κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ
        d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal ↥B.1).inertiaDeg C
            : ℕ) : ℕ∞) := by
  classical
  have := hDdim
  have hCκ : Function.Injective (algebraMap C κ) := by
    rw [IsScalarTower.algebraMap_eq C K κ]
    exact (algebraMap K κ).injective.comp (IsFractionRing.injective C K)
  have hCD : Function.Injective (algebraMap C D) := fun a b h => hCκ (by
    rw [IsScalarTower.algebraMap_apply C D κ, IsScalarTower.algebraMap_apply C D κ b, h])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hmC : maximalIdeal C = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ϖ ∈ maximalIdeal C := hmC ▸ Ideal.mem_span_singleton_self ϖ
  set ϖD : D := algebraMap C D ϖ with hϖD
  have hϖD0 : ϖD ≠ 0 := (map_ne_zero_iff _ hCD).mpr hϖ.ne_zero
  have hmCD : (maximalIdeal C).map (algebraMap C D) = Ideal.span {ϖD} := by
    rw [hmC, Ideal.map_span, Set.image_singleton]
  have hsurj : Function.Surjective ((residue D).comp (algebraMap C D)) := by
    intro x
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨c, hc⟩ := hDres d
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply]
    exact ((Ideal.Quotient.eq (I := maximalIdeal D)).mpr hc).symm
  have : Algebra.IsIntegral D D₁ := Algebra.IsIntegral.of_finite D D₁
  have hDD₁ : Function.Injective (algebraMap D D₁) := fun a b h => by
    have := congrArg (algebraMap D₁ κ) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact IsFractionRing.injective D κ this
  have hCD₁ : Function.Injective (algebraMap C D₁) := by
    rw [IsScalarTower.algebraMap_eq C D D₁]; exact hDD₁.comp hCD
  have hmCD₁ : (maximalIdeal C).map (algebraMap C D₁) = (Ideal.span {ϖD}).map (algebraMap D D₁) :=
    by
    rw [IsScalarTower.algebraMap_eq C D D₁, ← Ideal.map_map, hmCD]
  set N : Submodule D D₁ := LinearMap.range (Algebra.linearMap D D₁) with hN
  have hNfin : Module.length D (D₁ ⧸ N) ≠ ⊤ := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := D) (M := D₁)
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors D)
      (s.image (fun x : D₁ => algebraMap D₁ κ x))
    have hbN : ∀ x : D₁, (b : D) • x ∈ N := by
      intro x
      have hx : x ∈ Submodule.span D (s : Set D₁) := by rw [hs]; exact Submodule.mem_top
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · intro y hy
        obtain ⟨a, ha⟩ := hb (algebraMap D₁ κ y) (Finset.mem_image_of_mem _ hy)
        refine ⟨a, ?_⟩
        apply IsFractionRing.injective D₁ κ
        change algebraMap D₁ κ (algebraMap D D₁ a) = algebraMap D₁ κ ((b : D) • y)
        rw [← IsScalarTower.algebraMap_apply, ha, Algebra.smul_def, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply]
      · rw [smul_zero]; exact N.zero_mem
      · intro y z _ _ hy hz; rw [smul_add]; exact N.add_mem hy hz
      · intro a y _ hy; rw [smul_comm]; exact N.smul_mem a hy
    refine length_ne_top_of_smul_eq_zero hDdim (b : D) (nonZeroDivisors.ne_zero b.2) fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hbN x
  have hreg : ∀ m : D₁, ϖD • m = 0 → m = 0 := fun m hm => by
    rw [Algebra.smul_def, mul_eq_zero] at hm
    exact hm.resolve_left ((map_ne_zero_iff _ hDD₁).mpr hϖD0)
  have hlat := length_quotient_span_singleton_smul_top_eq ϖD hreg N hNfin
  have eN : ↥N ≃ₗ[D] D := (LinearEquiv.ofInjective (Algebra.linearMap D D₁) hDD₁).symm
  have hleft : Module.length D (↥N ⧸ ((Ideal.span {ϖD} : Ideal D) • (⊤ : Submodule D ↥N))) =
      Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) := by
    refine (Submodule.Quotient.equiv ((Ideal.span {ϖD} : Ideal D) • (⊤ : Submodule D ↥N))
      ((Ideal.span {ϖD} : Ideal D) • (⊤ : Submodule D D)) eN (by
        rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).length_eq.trans ?_
    · rw [hmCD, Submodule.ideal_span_singleton_smul]
      refine (Submodule.quotEquivOfEq _ _ ?_).length_eq
      ext d
      rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
      exact ⟨fun ⟨e, _, h⟩ => ⟨e,
        by rw [← h, smul_eq_mul, mul_comm]⟩, fun ⟨e, h⟩ => ⟨e, Submodule.mem_top, by
        rw [← h, smul_eq_mul, mul_comm]⟩⟩
  have hright : Module.length D (D₁ ⧸ ((Ideal.span {ϖD} : Ideal D) • (⊤ : Submodule D D₁))) =
      Module.length D (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) := by
    rw [Ideal.smul_top_eq_map, ← hmCD₁]
    exact (Submodule.Quotient.restrictScalarsEquiv D ((maximalIdeal C).map (algebraMap C
      D₁))).length_eq
  have hM0 : ∀ q : D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁), ϖD • q = 0 := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    change ϖD • Submodule.Quotient.mk x = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    rw [hϖD, ← IsScalarTower.algebraMap_apply C D D₁]
    exact Ideal.mem_map_of_mem _ hϖm
  have hMfin : Module.Finite D (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ D ((maximalIdeal C).map (algebraMap C
      D₁))).toLinearMap
      Ideal.Quotient.mk_surjective
  have hlenM : Module.length D (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) ≠ ⊤ :=
    length_ne_top_of_smul_eq_zero hDdim ϖD hϖD0 hM0
  have h1 : Module.length C (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) =
      Module.length D (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    Module.length_restrictScalars_eq_of_surjective_residue hsurj (Module.length_ne_top_iff.mp hlenM)
  have h2 : Module.length C (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) =
      Module.length (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    Module.length_eq_of_surjective (R := C ⧸ maximalIdeal C) (S := C) Ideal.Quotient.mk_surjective
  have := IsLocalRing.maximalIdeal.isMaximal C
  let : Field (C ⧸ maximalIdeal C) := Ideal.Quotient.field _
  have hflk : IsFiniteLength (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    by
    rw [← Module.length_ne_top_iff, ← h2, h1]; exact hlenM
  have : IsNoetherian (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hflk).1
  have : Module.Finite (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    inferInstance
  have h3 : Module.length (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) =
      Module.finrank (C ⧸ maximalIdeal C) (D₁ ⧸ (maximalIdeal C).map (algebraMap C D₁)) :=
    Module.length_eq_finrank _ _
  obtain ⟨hIfin, hsum⟩ := finrank_quotient_map_maximalIdeal_eq_finsum (C := C) K (D₁ := D₁) κ hCD₁
  have hDκ : ∀ d : D, algebraMap D κ d = algebraMap D₁ κ (algebraMap D D₁ d) := fun d =>
    IsScalarTower.algebraMap_apply D D₁ κ d
  have hD₁B : ∀ B : ValuationSubring κ, (∀ d : D, algebraMap D κ d ∈ B) → ∀ x : D₁, algebraMap D₁ κ
    x ∈ B := by
    intro B hB x
    let : Algebra D ↥B := ((algebraMap D κ).codRestrict B hB).toAlgebra
    have : IsScalarTower D ↥B κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hx : IsIntegral D (algebraMap D₁ κ x) :=
      (Algebra.IsIntegral.isIntegral (R := D) x).map (IsScalarTower.toAlgHom D D₁ κ)
    have hx' : IsIntegral ↥B (algebraMap D₁ κ x) := hx.tower_top
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff κ).mp inferInstance hx'
    rw [← hz]; exact z.2
  let e : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ x : D₁, algebraMap D₁ κ x
    ∈ B) ∧
        ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C} ≃
      {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ d ∈ B) ∧
        ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C} :=
    { toFun := fun B => ⟨B.1, B.2.1, fun d => by rw [hDκ]; exact B.2.2.1 _, B.2.2.2⟩
      invFun := fun B => ⟨B.1, B.2.1, hD₁B B.1 B.2.2.1, B.2.2.2⟩
      left_inv := fun B => rfl
      right_inv := fun B => rfl }
  have := hIfin
  have : Finite {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D
    κ d ∈ B) ∧
      ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C} := Finite.of_equiv _ e
  have : Algebra.IsIntegral K κ := Algebra.IsIntegral.of_finite K κ
  have hcentred : ∀ B : ValuationSubring κ, (∀ d : D, algebraMap D κ d ∈ B) → B ≠ ⊤ →
      ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C := by
    intro B hB hBtop
    have hCB : ∀ c : C, algebraMap C κ c ∈ B := fun c => by
      rw [IsScalarTower.algebraMap_apply C D κ]; exact hB _
    have hϖκ0 : algebraMap C κ ϖ ≠ 0 := (map_ne_zero_iff _ hCκ).mpr hϖ.ne_zero
    have hϖB : algebraMap C κ ϖ ∈ B.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or]
      refine Or.inr fun hinv => hBtop ?_
      have hKB : ∀ k : K, algebraMap K κ k ∈ B := by
        intro k
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) k
        have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
        obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
        obtain ⟨u, hu⟩ := hn
        have hbinv : (algebraMap C κ b)⁻¹ = algebraMap C κ u * ((algebraMap C κ ϖ)⁻¹) ^ n := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← mul_assoc, ← map_mul, hu, map_pow, inv_pow, mul_inv_cancel₀ (pow_ne_zero n hϖκ0)]
        rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
          div_eq_mul_inv, hbinv]
        exact B.mul_mem _ _ (hCB a) (B.mul_mem _ _ (hCB u) (pow_mem hinv n))
      let : Algebra K ↥B := ((algebraMap K κ).codRestrict B hKB).toAlgebra
      have : IsScalarTower K ↥B κ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      refine eq_top_iff.mpr fun x _ => ?_
      have hx' : IsIntegral ↥B x := (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
      obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff κ).mp inferInstance hx'
      rw [← hz]; exact z.2
    intro c
    constructor
    · intro hc
      by_contra hcm
      have hu : IsUnit c := by
        by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal c).mpr h)
      obtain ⟨u, rfl⟩ := hu
      rw [ValuationSubring.mem_nonunits_iff_or] at hc
      rcases hc with h | h
      · exact ((map_ne_zero_iff _ hCκ).mpr u.ne_zero) h
      · apply h
        have hui : (algebraMap C κ ↑u)⁻¹ = algebraMap C κ ↑u⁻¹ :=
          inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one])
        rw [hui]
        exact hCB _
    · intro hc
      rw [hmC, Ideal.mem_span_singleton'] at hc
      obtain ⟨c', rfl⟩ := hc
      rw [map_mul, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      refine ⟨B.mul_mem _ _ (hCB c') (hCB ϖ), ?_⟩
      have : (⟨algebraMap C κ c' * algebraMap C κ ϖ, B.mul_mem _ _ (hCB c') (hCB ϖ)⟩ : ↥B) =
          ⟨algebraMap C κ c', hCB c'⟩ * ⟨algebraMap C κ ϖ, hCB ϖ⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hϖB)
  have hfinite : {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite := by
    refine ((Set.finite_range (fun B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧
      (∀ d : D, algebraMap D κ d ∈ B) ∧ ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal
        C} => B.1)).insert
        ⊤).subset ?_
    intro B hB
    by_cases hBtop : B = ⊤
    · exact Or.inl hBtop
    · refine Or.inr ⟨⟨B, fun c => ?_, hB, hcentred B hB hBtop⟩, rfl⟩
      rw [IsScalarTower.algebraMap_apply C D κ]; exact hB _
  refine ⟨hfinite, ?_⟩
  rw [← hleft, hlat, hright, ← h1, h2, h3, hsum]
  exact finsum_eq_of_bijective e e.bijective (fun B => rfl)

end NormLength

theorem _root_.IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    {B : ValuationSubring κ | ∀ d : D, algebraMap D κ d ∈ B}.Finite ∧
    Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) =
      ∑ᶠ B : {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ
        d ∈ B) ∧
          ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C},
        ((letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
          (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal ↥B.1).inertiaDeg C
            : ℕ) : ℕ∞) := by
  obtain ⟨D₁, hfin, -, hloc⟩ :=
    IsDiscreteValuationRing.exists_finite_locallyPrincipalOverring (C := C) K (κ := κ) (A := D)
  have := hfin
  have : IsDedekindDomain ↥D₁ := NormLength.isDedekindDomain_of_locallyPrincipal hDdim D₁ hfin hloc
  have : IsFractionRing ↥D₁ κ := NormLength.isFractionRing_subalgebra κ D₁
  exact NormLength.core K hDmax hDres hDdim hDnf κ ↥D₁
end IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
