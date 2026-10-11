/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Util.WithWeakNamespace

/-!
# Unit-module and structure-sheaf Čech groups

For a two-affine-open cover, sections of the unit module and structure-sheaf sections give
canonically equivalent zeroth and first Čech groups.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry
namespace UnitComparison

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

/-- Čech sections of the unit module for the two-affine-open cover. -/
abbrev SU : TwoChartCech.Sections (𝒱.cover c) :=
  𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)
/-- Structure-sheaf Čech sections for the same cover. -/
abbrev SO : TwoChartCech.Sections (𝒱.cover c) := 𝒱.structureSheafSections c

theorem cechDiff_eq (s : (SU 𝒱 c).M0 × (SU 𝒱 c).M1) :
    (show (SO 𝒱 c).M01 from (SU 𝒱 c).cechDiff s)
      = (SO 𝒱 c).cechDiff (show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from s) := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, TwoChartCech.Cover.lineBundle_r0_apply,
      Units.val_one, one_mul]
  rfl

/-- Regard a compatible pair of unit-module sections as structure-sheaf sections. -/
def toFunH0 (x : (SU 𝒱 c).H0) : (SO 𝒱 c).H0 :=
  ⟨(show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← cechDiff_eq, hx]; rfl⟩

/-- Regard a compatible pair of structure-sheaf sections as unit-module sections. -/
def invFunH0 (x : (SO 𝒱 c).H0) : (SU 𝒱 c).H0 :=
  ⟨(show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx ⊢
    have := cechDiff_eq 𝒱 c (show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from x.1)
    exact (show (SU 𝒱 c).cechDiff _ = (show (SU 𝒱 c).M01 from (0 : (SO 𝒱 c).M01))
      from by rw [← hx]; exact this)⟩

/-- The canonical linear equivalence between the two zeroth Čech groups. -/
def equivH0 : (SU 𝒱 c).H0 ≃ₗ[R] (SO 𝒱 c).H0 where
  toFun := toFunH0 𝒱 c
  invFun := invFunH0 𝒱 c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem range_eq :
    (show Submodule R (SO 𝒱 c).M01 from LinearMap.range (SU 𝒱 c).cechDiff)
      = LinearMap.range (SO 𝒱 c).cechDiff := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from s), (cechDiff_eq 𝒱 c s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from s), cechDiff_eq 𝒱 c _⟩

/-- The canonical linear equivalence between the two first Čech groups. -/
def equivH1 : (SU 𝒱 c).H1 ≃ₗ[R] (SO 𝒱 c).H1 :=
  Submodule.quotEquivOfEq _ _ (range_eq 𝒱 c)

end UnitComparison

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

with_weak_namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover TwoAffineOpenCover in
with_weak_namespace _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
theorem exists_sectionsOf_unit_equiv_structureSheafSections
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) :
    ∃ (e0 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
          (𝒱.structureSheafSections c).H0)
      (e1 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
          (𝒱.structureSheafSections c).H1),
      (∀ x, ((e0 x : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) = x.1) ∧
      (∀ y : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01,
          e1 (Submodule.Quotient.mk y)
            = Submodule.Quotient.mk (show (𝒱.structureSheafSections c).M01 from y)) :=
  ⟨UnitComparison.equivH0 𝒱 c, UnitComparison.equivH1 𝒱 c, fun _ => rfl, fun _ => rfl⟩

end
end Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
