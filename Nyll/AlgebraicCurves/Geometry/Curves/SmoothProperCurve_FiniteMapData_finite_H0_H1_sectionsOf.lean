/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Sections_finite_H1_of_chartFinite
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCech_Sections_finite_H0_of_chartFinite
import Nyll.SchemeTheory.Modules.LocallyTrivialSectionsLocalization
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Finite cohomology from finite-map data on a curve

Finite-map data on a smooth proper curve gives finite zeroth and first two-chart
cohomology for a module that is locally trivial.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.NeronModelInfra

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace SmoothProperCurve
open _root_.AlgebraicGeometry.SmoothProperCurve
namespace FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry
namespace SectionsOfFinite

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : FiniteMapData c ε) (M : C.Modules)
  (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
    Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))

open AlgebraicGeometry.Scheme.TwoAffineOpenCover

/-- Restriction in the structure sheaf between the specified open subsets. -/
abbrev rO {W₁ W₂ : C.Opens} (h : W₂ ≤ W₁) : Γ(C, W₁) → Γ(C, W₂) := fun x => (C.presheaf.map
    (homOfLE h).op).hom x

theorem VU_eq_basicOpen_g : 𝔉.V ⊓ 𝔉.U = C.basicOpen 𝔉.g := by rw [inf_comm, 𝔉.inf_eq_basicOpen_g]
theorem VU_eq_basicOpen_f : 𝔉.V ⊓ 𝔉.U = C.basicOpen 𝔉.f := by rw [inf_comm, 𝔉.inf_eq_basicOpen]
include htriv in
theorem loc_transport {W₁ W₂ : C.Opens} (hW₁ : IsAffineOpen W₁) (h : Γ(C, W₁)) (hW₂ : W₂ =
    C.basicOpen h)
    (hle : W₂ ≤ W₁) :
    (∀ x : Γ(M, W₂), ∃ (n : ℕ) (y : Γ(M, W₁)), M.presheaf.map (homOfLE hle).op y = rO hle h ^ n
        • x) ∧
    (∀ y : Γ(M, W₁), M.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, (h ^ n : Γ(C, W₁)) • y =
        0) := by
  subst hW₂
  have := AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv
      ⟨W₁, hW₁⟩ h
  refine ⟨fun x => ?_, fun y hy => this.2 y hy⟩
  obtain ⟨n, y, hy⟩ := this.1 x
  exact ⟨n, y, by rw [hy, map_pow]⟩

theorem finite_adjoin_of_aeval_finite {A : Type u} [CommRing A] [Algebra R A] (f : A)
    (hf : (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.Finite) :
    Module.Finite (Algebra.adjoin R ({f} : Set A)) A := by
  let : Algebra (Polynomial R) A := (Polynomial.aeval f : Polynomial R →ₐ[R] A).toRingHom.toAlgebra
  have : Module.Finite (Polynomial R) A := hf
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite (Polynomial R) A)
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span (Polynomial R) (s : Set A) := by rw [hs]; trivial
  refine Submodule.span_induction (p := fun y _ => y ∈ Submodule.span (Algebra.adjoin R ({f} :
      Set A)) (s : Set A))
    (fun y hy => Submodule.subset_span hy) (Submodule.zero_mem _) (fun y z _ _ hy hz =>
        Submodule.add_mem _ hy hz)
    (fun p y _ hy => ?_) hx
  have hp : (Polynomial.aeval f p : A) ∈ Algebra.adjoin R ({f} : Set A) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
  have : (p • y : A) = (⟨Polynomial.aeval f p, hp⟩ : Algebra.adjoin R ({f} : Set A)) • y := rfl
  change p • y ∈ Submodule.span (Algebra.adjoin R ({f} : Set A)) (s : Set A)
  rw [this]
  exact Submodule.smul_mem _ _ hy

end SectionsOfFinite

open SectionsOfFinite AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem finite_H0_H1_sectionsOf'
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
          V.toScheme.ringCatSheaf)) :
    Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H1 := by
  let 𝒱 := 𝔉.twoAffineOpenCover
  let 𝒰 := 𝒱.cover c
  let S := 𝒱.sectionsOf c M
  let gA0 : 𝒰.A0 := 𝔉.g
  let fA1 : 𝒰.A1 := 𝔉.f
  have hfg : 𝒰.ρ0 gA0 * 𝒰.ρ1 fA1 = 1 := by
    rw [cover_ρ0_apply, cover_ρ1_apply]
    erw [mul_comm]
    have h := congrArg (rO (C := C) (inf_comm 𝔉.V 𝔉.U).le) 𝔉.res_f_mul_res_g
    simp only [rO, map_mul, map_one] at h
    rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp] at h
    exact h
  have hfinV : Module.Finite Γ(C, 𝔉.V) Γ(M, 𝔉.V) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial M htriv ⟨𝔉.V,
        𝔉.isAffineOpen_V⟩
  have hfinU : Module.Finite Γ(C, 𝔉.U) Γ(M, 𝔉.U) :=
    AlgebraicGeometry.Scheme.Modules.finite_sections_of_locallyTrivial M htriv ⟨𝔉.U,
        𝔉.isAffineOpen_U⟩
  let : Algebra R 𝒰.A0 := 𝒰.A0_algebra
  let : Algebra R 𝒰.A1 := 𝒰.A1_algebra
  have hfin0 : Module.Finite (Algebra.adjoin R ({gA0} : Set 𝒰.A0)) S.M0 := by
    have : Module.Finite (Algebra.adjoin R ({gA0} : Set 𝒰.A0)) 𝒰.A0 :=
        finite_adjoin_of_aeval_finite gA0 𝔉.finite_g
    have : Module.Finite 𝒰.A0 S.M0 := hfinV
    exact Module.Finite.trans 𝒰.A0 S.M0
  have hfin1 : Module.Finite (Algebra.adjoin R ({fA1} : Set 𝒰.A1)) S.M1 := by
    have : Module.Finite (Algebra.adjoin R ({fA1} : Set 𝒰.A1)) 𝒰.A1 :=
        finite_adjoin_of_aeval_finite fA1 𝔉.finite_f
    have : Module.Finite 𝒰.A1 S.M1 := hfinU
    exact Module.Finite.trans 𝒰.A1 S.M1
  obtain ⟨loc0, tors0⟩ := loc_transport M htriv 𝔉.isAffineOpen_V 𝔉.g
      (SectionsOfFinite.VU_eq_basicOpen_g 𝔉) inf_le_left
  obtain ⟨loc1, tors1⟩ := loc_transport M htriv 𝔉.isAffineOpen_U 𝔉.f
      (SectionsOfFinite.VU_eq_basicOpen_f 𝔉) inf_le_right
  have hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 gA0) ^ n • m ∈ LinearMap.range S.r0 := by
    intro m
    obtain ⟨n, y, hy⟩ := loc0 m
    exact ⟨n, y, by erw [sectionsOf_r0_apply, cover_ρ0_apply]; exact hy⟩
  have hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 fA1) ^ n • m ∈ LinearMap.range S.r1 := by
    intro m
    obtain ⟨n, y, hy⟩ := loc1 m
    exact ⟨n, y, by erw [sectionsOf_r1_apply, cover_ρ1_apply]; exact hy⟩
  have htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, gA0 ^ n • x = 0 := by
    intro x hx
    erw [sectionsOf_r0_apply] at hx
    exact tors0 x hx
  have htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, fA1 ^ n • y = 0 := by
    intro y hy
    erw [sectionsOf_r1_apply] at hy
    exact tors1 y hy
  exact ⟨TwoChartCech.Sections.finite_H0_of_chartFinite S gA0 fA1 hfg hfin0 hfin1 hloc0 hloc1
      htors0 htors1,
    TwoChartCech.Sections.finite_H1_of_chartFinite S gA0 fA1 hfg hfin0 hloc0 hloc1⟩

end AlgebraicGeometry.SmoothProperCurve.FiniteMapData

theorem _root_.AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_sectionsOf
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (M : C.Modules)
    (htriv : ∀ x : C, ∃ (V : C.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
          V.toScheme.ringCatSheaf)) :
    Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H0 ∧
      Module.Finite R (𝔉.twoAffineOpenCover.sectionsOf c M).H1 :=
  AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_sectionsOf' 𝔉 M htriv

end
end SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
