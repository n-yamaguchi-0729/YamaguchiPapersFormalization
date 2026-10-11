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

import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.Ideal

/-!
# Fiber Localization Quotient
-/

noncomputable section

universe u v w

open TensorProduct

namespace FiberLocalizationQuotient

section FiberLemmas

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (p : Ideal A) [p.IsPrime]

private theorem one_tmul_eq_zero_of_mem_map
    (w : B) (hw : w ∈ p.map (algebraMap A B)) :
    (1 : p.ResidueField) ⊗ₜ[A] w = 0 := by
  have hle : p.map (algebraMap A B) ≤ RingHom.ker
      (Algebra.TensorProduct.includeRight
        (R := A) (A := p.ResidueField) (B := B)).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h0 : algebraMap A p.ResidueField a = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr ha
    change (1 : p.ResidueField) ⊗ₜ[A] (algebraMap A B a) = 0
    calc (1 : p.ResidueField) ⊗ₜ[A] (algebraMap A B a)
        = algebraMap A (p.Fiber B) a := (Algebra.TensorProduct.algebraMap_apply' a).symm
      _ = 0 := by
          rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B), h0, map_zero]
  have hker := hle hw
  rw [RingHom.mem_ker] at hker
  simpa using hker

private theorem isUnit_algebraMap_fiber_of_notMem
    (r : A) (hr : r ∉ p) : IsUnit (algebraMap A (p.Fiber B) r) := by
  rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B)]
  exact (isUnit_iff_ne_zero.mpr
    fun h0 => hr (Ideal.algebraMap_residueField_eq_zero.mp h0)).map _

private theorem mem_iff_one_tmul_mem
    (q : Ideal B) (Q : Ideal (p.Fiber B))
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) (b : B) :
    b ∈ q ↔ (1 : p.ResidueField) ⊗ₜ[A] b ∈ Q := by
  conv_lhs => rw [← hQq]
  rw [Ideal.mem_comap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]

end FiberLemmas

private theorem quotientComposite_eq_zero
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq]
    (a : A) (ha : a ∈ p) :
    ((Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))).comp
      ((algebraMap B Bq).comp (algebraMap A B))) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))

private theorem isUnit_quotientMk_of_notMem
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (b : B) (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
      (algebraMap B Bq b)) :=
  (IsLocalization.map_units (M := q.primeCompl) Bq ⟨b, hb⟩).map (Ideal.Quotient.mk _)

private noncomputable def quotientMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq] :
    A ⧸ p →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  Ideal.Quotient.lift p
    ((Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))).comp
      ((algebraMap B Bq).comp (algebraMap A B)))
    (quotientComposite_eq_zero p Bq)

private theorem quotientMap_mk
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq] (a : A) :
    quotientMap p Bq (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) :=
  rfl

private theorem quotientMap_isUnit
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (y : nonZeroDivisors (A ⧸ p)) : IsUnit (quotientMap (B := B) p Bq y) := by
  have hpq : p = q.comap (algebraMap A B) := Ideal.LiesOver.over
  obtain ⟨y, hy⟩ := y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∉ p := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hy) (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hb : algebraMap A B a ∉ q := fun hin =>
    ha (by rw [hpq]; exact Ideal.mem_comap.mpr hin)
  change IsUnit (quotientMap (B := B) p Bq (Ideal.Quotient.mk p a))
  rw [quotientMap_mk]
  exact isUnit_quotientMk_of_notMem p q Bq (algebraMap A B a) hb

private noncomputable def residueFieldMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] :
    p.ResidueField →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  IsLocalization.lift (M := nonZeroDivisors (A ⧸ p)) (quotientMap_isUnit p q Bq)

private theorem residueFieldMap_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] (a : A) :
    residueFieldMap p q Bq (algebraMap A p.ResidueField a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) := by
  change IsLocalization.lift (M := nonZeroDivisors (A ⧸ p)) (quotientMap_isUnit p q Bq)
      (algebraMap A p.ResidueField a) = _
  rw [IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField, IsLocalization.lift_eq,
    Ideal.Quotient.algebraMap_eq, quotientMap_mk]

/-- The map from the fiber algebra to the quotient of the localization by the base prime. -/
noncomputable def localizationQuotientMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] :
    p.Fiber B →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  letI : Algebra A Bq := ((algebraMap B Bq).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B Bq := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.productMap
    { toRingHom := residueFieldMap p q Bq
      commutes' := fun a => by
        change residueFieldMap p q Bq (algebraMap A p.ResidueField a) = _
        rw [residueFieldMap_algebraMap]
        rfl }
    (IsScalarTower.toAlgHom A B
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)))).toRingHom

private theorem localizationQuotientMap_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (x : p.ResidueField) (b : B) :
    localizationQuotientMap p q Bq (x ⊗ₜ[A] b) =
      residueFieldMap p q Bq x *
        Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
          (algebraMap B Bq b) :=
  rfl

theorem localizationQuotientMap_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (b : B) :
    localizationQuotientMap p q Bq ((1 : p.ResidueField) ⊗ₜ[A] b) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq b) := by
  rw [localizationQuotientMap_tmul, map_one, one_mul]

private theorem localizationQuotientMap_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (a : A) :
    localizationQuotientMap p q Bq (algebraMap A (p.Fiber B) a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, localizationQuotientMap_tmul,
    residueFieldMap_algebraMap, map_one, map_one, mul_one]

section LocalizationMap

theorem isLocalization_localizationQuotientMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber B)) [Q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) :
    @IsLocalization (p.Fiber B) _ Q.primeCompl
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) _
      (localizationQuotientMap p q Bq).toAlgebra := by
  have hQp : Q.IsPrime := inferInstance
  let : Algebra (p.Fiber B)
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) :=
    (localizationQuotientMap p q Bq).toAlgebra
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p x
    have hu : IsUnit (algebraMap A (p.Fiber B) r) :=
      isUnit_algebraMap_fiber_of_notMem p r hr
    have h1s : (1 : p.ResidueField) ⊗ₜ[A] s ∉ Q := by
      intro hmem'
      rw [← hrs, Algebra.smul_def] at hmem'
      rcases hQp.mem_or_mem hmem' with h | h
      · exact hQp.ne_top (Q.eq_top_of_isUnit_mem h hu)
      · exact hx h
    have hs : s ∉ q := fun hsq =>
      h1s ((mem_iff_one_tmul_mem p q Q hQq s).mp hsq)
    change IsUnit (localizationQuotientMap p q Bq x)
    have hchain :
        Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
            (algebraMap B Bq (algebraMap A B r)) * localizationQuotientMap p q Bq x =
          localizationQuotientMap p q Bq ((1 : p.ResidueField) ⊗ₜ[A] s) := by
      rw [← localizationQuotientMap_algebraMap p q Bq r, ← map_mul, ← Algebra.smul_def,
        hrs]
    have hprod : IsUnit
        (Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
          (algebraMap B Bq (algebraMap A B r)) * localizationQuotientMap p q Bq x) := by
      rw [hchain, localizationQuotientMap_one_tmul]
      exact isUnit_quotientMk_of_notMem p q Bq s hs
    exact isUnit_of_mul_isUnit_right hprod
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (M := q.primeCompl) (S := Bq) w
    refine ⟨⟨(1 : p.ResidueField) ⊗ₜ[A] b,
      ⟨(1 : p.ResidueField) ⊗ₜ[A] (s : B),
        fun hc => s.2 ((mem_iff_one_tmul_mem p q Q hQq (s : B)).mpr hc)⟩⟩, ?_⟩
    change Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (IsLocalization.mk' Bq b s) *
        localizationQuotientMap p q Bq ((1 : p.ResidueField) ⊗ₜ[A] (s : B)) =
      localizationQuotientMap p q Bq ((1 : p.ResidueField) ⊗ₜ[A] b)
    rw [localizationQuotientMap_one_tmul, localizationQuotientMap_one_tmul, ← map_mul,
      IsLocalization.mk'_spec]
  · intro x y hxy
    replace hxy : localizationQuotientMap p q Bq x = localizationQuotientMap p q Bq y := hxy
    obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p (x - y)
    have hd : localizationQuotientMap p q Bq (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hs0 : Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq s) = 0 := by
      rw [← localizationQuotientMap_one_tmul p q Bq s, ← hrs, Algebra.smul_def, map_mul,
        hd, mul_zero]
    have hsJ : algebraMap B Bq s ∈ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hs0
    obtain ⟨⟨j, u⟩, hju⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := q.primeCompl) (S := Bq)).mp hsJ
    have h0 : algebraMap B Bq (s * (u : B) - (j : B)) = 0 := by
      rw [map_sub, map_mul, hju, sub_self]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (M := q.primeCompl)
      (S := Bq) (s * (u : B) - (j : B))).mp h0
    rw [mul_sub, sub_eq_zero] at hm
    have hvs : (((u : B) * (m : B)) * s) ∈ p.map (algebraMap A B) := by
      have hveq : ((u : B) * (m : B)) * s = (m : B) * (s * (u : B)) := by ac_rfl
      rw [hveq, hm]
      exact Ideal.mul_mem_left _ _ j.2
    have hzero : (1 : p.ResidueField) ⊗ₜ[A] (((u : B) * (m : B)) * s) = 0 :=
      one_tmul_eq_zero_of_mem_map p _ hvs
    have hv : (u : B) * (m : B) ∈ q.primeCompl := q.primeCompl.mul_mem u.2 m.2
    have hc : ((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) * (x - y) = 0 := by
      have hu := isUnit_algebraMap_fiber_of_notMem (B := B) p r hr
      refine (hu.mul_right_eq_zero).mp ?_
      have hswap : algebraMap A (p.Fiber B) r *
          (((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) * (x - y)) =
          ((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) *
            (algebraMap A (p.Fiber B) r * (x - y)) := by ac_rfl
      rw [hswap, ← Algebra.smul_def, hrs, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact hzero
    refine ⟨⟨(1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B)),
      fun hQm => hv
        ((mem_iff_one_tmul_mem p q Q hQq ((u : B) * (m : B))).mpr hQm)⟩, ?_⟩
    rw [mul_sub] at hc
    exact sub_eq_zero.mp hc

end LocalizationMap

section MaximalIdeal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (p : Ideal A) [p.IsPrime]
variable (Bq : Type w) [CommRing Bq] [Algebra B Bq]

theorem maximalIdeal_map_eq
    (Ap : Type w) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p]
    [IsLocalRing Ap] (g : Ap →+* Bq)
    (hg : g.comp (algebraMap A Ap) = (algebraMap B Bq).comp (algebraMap A B)) :
    (IsLocalRing.maximalIdeal Ap).map g =
      (p.map (algebraMap A B)).map (algebraMap B Bq) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Ap, Ideal.map_map, hg,
    ← Ideal.map_map]

end MaximalIdeal

end FiberLocalizationQuotient

end
