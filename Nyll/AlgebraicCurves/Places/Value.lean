/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Value
-/

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem residue_algebraMap (c : K) :
    residue v.toValuationSubring (algebraMap K v.toValuationSubring c)
      = algebraMap K v.ResidueField c := by
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField c,
    ResidueField.algebraMap_eq]

/-- The function is integral at the place and its residue is the specified base-field value. -/
def HasValue (g : F) (a : K) : Prop :=
  ∃ h : g ∈ v.toValuationSubring,
    residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a

theorem hasValue_iff (g : F) (a : K) :
    v.HasValue g a ↔ ∃ h : g ∈ v.toValuationSubring,
      residue v.toValuationSubring ⟨g, h⟩ = algebraMap K v.ResidueField a :=
  Iff.rfl

variable {v}

theorem HasValue.mem {g : F} {a : K} (h : v.HasValue g a) : g ∈ v.toValuationSubring :=
  h.1

theorem HasValue.residue_eq {g : F} {a : K} (h : v.HasValue g a) :
    residue v.toValuationSubring ⟨g, h.mem⟩ = algebraMap K v.ResidueField a :=
  h.2

variable (v) in
theorem hasValue_one : v.HasValue (1 : F) 1 :=
  ⟨one_mem _, by rw [map_one]; exact map_one (residue v.toValuationSubring)⟩

variable (v) in
theorem hasValue_algebraMap (c : K) : v.HasValue (algebraMap K F c) c :=
  ⟨v.algebraMap_mem' c, v.residue_algebraMap c⟩

theorem HasValue.mul {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g * g') (a * a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨mul_mem hg hg', ?_⟩
  have hx : (⟨g * g', mul_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ * ⟨g', hg'⟩ := rfl
  rw [hx, map_mul, hr, hr', map_mul]

theorem HasValue.isUnit {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    IsUnit (⟨g, h.mem⟩ : v.toValuationSubring) := by
  rw [← residue_ne_zero_iff_isUnit, h.residue_eq]
  exact (map_ne_zero _).mpr ha

theorem HasValue.ne_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : g ≠ 0 := by
  intro hg
  apply (h.isUnit ha).ne_zero
  exact Subtype.ext hg

theorem HasValue.inv {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) :
    v.HasValue g⁻¹ a⁻¹ := by
  obtain ⟨u, hu⟩ := h.isUnit ha
  have hcoe : ((u : v.toValuationSubring) : F) = g := by rw [hu]
  have hinv : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = g⁻¹ := by
    have h1 : g * (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        OneMemClass.coe_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hmem : g⁻¹ ∈ v.toValuationSubring := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx : (⟨g⁻¹, hmem⟩ : v.toValuationSubring)
      = ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) :=
    Subtype.ext hinv.symm
  rw [hx, map_units_inv, hu, h.residue_eq, map_inv₀]

theorem HasValue.unique {g : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g a') :
    a = a' :=
  (algebraMap K v.ResidueField).injective (h.residue_eq.symm.trans h'.residue_eq)

theorem HasValue.ord_eq_zero {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) : v.ord g = 0 := by
  have h0 := v.ord_coe_unit (h.isUnit ha).unit
  rwa [IsUnit.unit_spec] at h0

variable (v) in
theorem exists_isUnit_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

variable (v) in
theorem exists_hasValue_of_surjective (hv : Function.Surjective (algebraMap K v.ResidueField))
    {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ a : K, v.HasValue g a ∧ (IsUnit (⟨g, hg⟩ : v.toValuationSubring) → a ≠ 0) := by
  obtain ⟨a, ha⟩ := hv (residue v.toValuationSubring ⟨g, hg⟩)
  refine ⟨a, ⟨hg, ha.symm⟩, fun hu h0 => ?_⟩
  rw [← residue_ne_zero_iff_isUnit, ← ha, h0, map_zero] at hu
  exact hu rfl

end Place

end AlgebraicCurve

end
