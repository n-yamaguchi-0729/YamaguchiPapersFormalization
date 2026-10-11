/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Sections_finite_H1_of_chartFinite
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Sections_finite_H0_of_chartFinite
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Finite cohomology of line bundles on two charts

Localization expresses sections on a basic open using a denominator power.
Finite maps on the two affine charts then give finite zeroth and first Cech
cohomology for the associated line bundles.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
namespace ChartFiniteInstances

variable {X : Scheme.{u}}

/-- Restrict a structure-sheaf section to a smaller open subset. -/
abbrev res {U W : X.Opens} (h : W ≤ U) : Γ(X, U) → Γ(X, W) := fun x => (X.presheaf.map (homOfLE
    h).op).hom x

theorem res_res' {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    res h₃₂ (res h₂₁ x) = res (h₃₂.trans h₂₁) x := by
  change (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) = _
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl

theorem res_self {V : X.Opens} (h : V ≤ V) (x : Γ(X, V)) : res h x = x := by
  change (X.presheaf.map (homOfLE h).op).hom x = x
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem exists_pow_mul_eq_res {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W =
    X.basicOpen f)
    (m : Γ(X, W)) :
    ∃ (x : Γ(X, U)) (n : ℕ), res (hW.le.trans (X.basicOpen_le f)) f ^ n * m
      = res (hW.le.trans (X.basicOpen_le f)) x := by
  subst hW
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) m
  refine ⟨x, n, ?_⟩
  rw [mul_comm]
  simpa only [res, Scheme.algebra_section_section_basicOpen,
    RingHom.algebraMap_toAlgebra, map_pow] using h

theorem exists_pow_mul_eq_zero {U W : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (hW : W =
    X.basicOpen f)
    (x : Γ(X, U)) (hx : res (hW.le.trans (X.basicOpen_le f)) x = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  subst hW
  have := hU.isLocalization_basicOpen f
  have hx' : algebraMap Γ(X, U) Γ(X, X.basicOpen f) x = 0 := hx
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)] at hx'
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := hx'
  exact ⟨n, hn⟩

theorem finite_adjoin_of_aeval_finite {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R
    A] (f : A)
    (h : (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.Finite) :
    Module.Finite (Algebra.adjoin R ({f} : Set A)) A := by
  let : Algebra (Polynomial R) A := (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.toAlgebra
  have : Module.Finite (Polynomial R) A := h
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite (Polynomial R) A)
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span (Polynomial R) (s : Set A) := by rw [hs]; trivial
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (Algebra.adjoin R ({f} : Set
      A)) (s : Set A))
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _) (fun y z _ _ hy hz =>
        Submodule.add_mem _ hy hz)
    (fun p y _ hy => ?_) hx
  have hp : (Polynomial.aeval f p : A) ∈ Algebra.adjoin R ({f} : Set A) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
  have : (p • y : A) = (⟨Polynomial.aeval f p, hp⟩ : Algebra.adjoin R ({f} : Set A)) • y := rfl
  change p • y ∈ Submodule.span (Algebra.adjoin R ({f} : Set A)) (s : Set A)
  rw [this]
  exact Submodule.smul_mem _ _ hy

end ChartFiniteInstances
end AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SmoothProperCurve
open _root_.AlgebraicGeometry.SmoothProperCurve
namespace FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
with_weak_namespace _root_.AlgebraicCurves.Geometry.Curves.Proofs
with_weak_namespace SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle
open AlgebraicGeometry.Scheme.TwoAffineOpenCover.ChartFiniteInstances

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : FiniteMapData c ε)

theorem VU_le_U : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.U := inf_le_right
theorem VU_le_V : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.V := inf_le_left
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.VU_eq_basicOpen_g : 𝔉.V ⊓
    𝔉.U = C.basicOpen 𝔉.g := by rw [inf_comm, 𝔉.inf_eq_basicOpen_g]
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.VU_eq_basicOpen_f : 𝔉.V ⊓
    𝔉.U = C.basicOpen 𝔉.f := by rw [inf_comm, 𝔉.inf_eq_basicOpen]

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
variable (c) in
private abbrev _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.gA0 :
    (𝔉.twoAffineOpenCover.cover c).A0 := 𝔉.g
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
variable (c) in
private abbrev _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.fA1 :
    (𝔉.twoAffineOpenCover.cover c).A1 := 𝔉.f

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.ρ0_g_mul_ρ1_f :
    (𝔉.twoAffineOpenCover.cover c).ρ0 (𝔉.gA0 c) * (𝔉.twoAffineOpenCover.cover c).ρ1 (𝔉.fA1 c) = 1 :=
        by
  change (C.presheaf.map (homOfLE (inf_le_left : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.V)).op).hom 𝔉.g *
    (C.presheaf.map (homOfLE (inf_le_right : 𝔉.V ⊓ 𝔉.U ≤ 𝔉.U)).op).hom 𝔉.f = 1
  rw [mul_comm]
  have h := congrArg (res (X := C) (inf_comm 𝔉.V 𝔉.U).le) 𝔉.res_f_mul_res_g
  simp only [res, map_mul, map_one] at h
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp] at h
  exact h

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.loc0 (m :
    (𝔉.twoAffineOpenCover.cover c).A01) :
    ∃ (x : (𝔉.twoAffineOpenCover.cover c).A0) (n : ℕ),
      (𝔉.twoAffineOpenCover.cover c).ρ0 (𝔉.gA0 c) ^ n * m = (𝔉.twoAffineOpenCover.cover c).ρ0 x :=
          by
  obtain ⟨x, n, h⟩ := exists_pow_mul_eq_res 𝔉.isAffineOpen_V 𝔉.g 𝔉.VU_eq_basicOpen_g m
  exact ⟨x, n, h⟩

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.loc1 (m :
    (𝔉.twoAffineOpenCover.cover c).A01) :
    ∃ (y : (𝔉.twoAffineOpenCover.cover c).A1) (n : ℕ),
      (𝔉.twoAffineOpenCover.cover c).ρ1 (𝔉.fA1 c) ^ n * m = (𝔉.twoAffineOpenCover.cover c).ρ1 y :=
          by
  obtain ⟨y, n, h⟩ := exists_pow_mul_eq_res 𝔉.isAffineOpen_U 𝔉.f 𝔉.VU_eq_basicOpen_f m
  exact ⟨y, n, h⟩

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.tors0 (x :
    (𝔉.twoAffineOpenCover.cover c).A0) (hx : (𝔉.twoAffineOpenCover.cover c).ρ0 x = 0) :
    ∃ n : ℕ, 𝔉.gA0 c ^ n * x = 0 :=
  exists_pow_mul_eq_zero 𝔉.isAffineOpen_V 𝔉.g 𝔉.VU_eq_basicOpen_g x hx

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.tors1 (y :
    (𝔉.twoAffineOpenCover.cover c).A1) (hy : (𝔉.twoAffineOpenCover.cover c).ρ1 y = 0) :
    ∃ n : ℕ, 𝔉.fA1 c ^ n * y = 0 :=
  exists_pow_mul_eq_zero 𝔉.isAffineOpen_U 𝔉.f 𝔉.VU_eq_basicOpen_f y hy

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData

private theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.chartFinite_lineBundle (t :
    (𝔉.twoAffineOpenCover.cover c).A01ˣ) :
    let 𝒰 := 𝔉.twoAffineOpenCover.cover c
    let S := 𝔉.twoAffineOpenCover.lineBundleSections c t
    (𝒰.ρ0 (𝔉.gA0 c) * 𝒰.ρ1 (𝔉.fA1 c) = 1) ∧
    Module.Finite (Algebra.adjoin R ({𝔉.gA0 c} : Set 𝒰.A0)) S.M0 ∧
    Module.Finite (Algebra.adjoin R ({𝔉.fA1 c} : Set 𝒰.A1)) S.M1 ∧
    (∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 (𝔉.gA0 c)) ^ n • m ∈ LinearMap.range S.r0) ∧
    (∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 (𝔉.fA1 c)) ^ n • m ∈ LinearMap.range S.r1) ∧
    (∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, 𝔉.gA0 c ^ n • x = 0) ∧
    (∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, 𝔉.fA1 c ^ n • y = 0) := by
  intro 𝒰 S
  refine ⟨𝔉.ρ0_g_mul_ρ1_f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finite_adjoin_of_aeval_finite (𝔉.gA0 c) 𝔉.finite_g
  · exact finite_adjoin_of_aeval_finite (𝔉.fA1 c) 𝔉.finite_f
  · intro m
    obtain ⟨x, n, h⟩ := 𝔉.loc0 m
    exact ⟨n, x, by rw [TwoChartCech.Cover.lineBundle_r0_apply, smul_eq_mul]; exact h.symm⟩
  · intro m
    obtain ⟨y, n, h⟩ := 𝔉.loc1 ((↑t⁻¹ : 𝒰.A01) * m)
    refine ⟨n, y, ?_⟩
    rw [TwoChartCech.Cover.lineBundle_r1_apply, smul_eq_mul, ← h, mul_left_comm, ← mul_assoc (t :
        𝒰.A01),
      Units.mul_inv, one_mul]
  · intro x hx
    rw [TwoChartCech.Cover.lineBundle_r0_apply] at hx
    obtain ⟨n, hn⟩ := 𝔉.tors0 x hx
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩
  · intro y hy
    rw [TwoChartCech.Cover.lineBundle_r1_apply] at hy
    obtain ⟨n, hn⟩ := 𝔉.tors1 y ((Units.mul_right_eq_zero t).mp hy)
    exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
end AlgebraicGeometry.SmoothProperCurve.FiniteMapData

theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_lineBundle
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (t : (𝔉.twoAffineOpenCover.cover c).A01ˣ) :
    Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.lineBundleSections c t).H1 := by
  obtain ⟨hfg, hfin0, hfin1, hloc0, hloc1, htors0, htors1⟩ := 𝔉.chartFinite_lineBundle t
  exact ⟨TwoChartCech.Sections.finite_H0_of_chartFinite _ (𝔉.gA0 c) (𝔉.fA1 c) hfg hfin0 hfin1 hloc0
      hloc1 htors0 htors1,
    TwoChartCech.Sections.finite_H1_of_chartFinite _ (𝔉.gA0 c) (𝔉.fA1 c) hfg hfin0 hloc0 hloc1⟩

end
end SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
