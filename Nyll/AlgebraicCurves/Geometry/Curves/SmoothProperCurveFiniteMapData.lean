/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Mathlib.RingTheory.Etale.Basic

/-!
# Finite coordinate maps on a pointed relative curve

Two affine charts cover the curve, with reciprocal coordinates on their intersection.
The coordinate maps are finite, and their level sets have the specified common free rank.
The associated affine cover and the generic étaleness condition are constructed from this data.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.SmoothProperCurve

/-- Finite coordinate maps on complementary affine charts of a curve with a section. -/
structure FiniteMapData {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) where
  /-- The affine chart complementary to the image of the chosen section. -/
  U : C.Opens
  /-- The second affine chart, which contains the image of the chosen section. -/
  V : C.Opens
  /-- The coordinate on the chart complementary to the section. -/
  f : Γ(C, U)
  /-- The coordinate on the second affine chart. -/
  g : Γ(C, V)
  /-- The common rank of the finite free coordinate level sets. -/
  m : ℕ
  /-- The chart complementary to the section is affine. -/
  isAffineOpen_U : IsAffineOpen U
  /-- The second chart is affine. -/
  isAffineOpen_V : IsAffineOpen V
  /-- The two affine charts cover the curve. -/
  sup_eq_top : U ⊔ V = ⊤
  /-- A point belongs to the first chart exactly when it is outside the section image. -/
  mem_U_iff : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base
  /-- The chart intersection is the basic open where the first coordinate is invertible. -/
  inf_eq_basicOpen : U ⊓ V = C.basicOpen f
  /-- The chart intersection is also the basic open where the second coordinate is invertible. -/
  inf_eq_basicOpen_g : U ⊓ V = C.basicOpen g
  /-- The restrictions of the two coordinates to the intersection multiply to one. -/
  res_f_mul_res_g : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1
  /-- The polynomial coordinate map on the first chart is finite. -/
  finite_f : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite
  /-- The polynomial coordinate map on the second chart is finite. -/
  finite_g : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite
  /-- Over every local base algebra, each first-coordinate level set is finite free of rank m. -/
  levelSet_free : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
      Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) = m

namespace FiniteMapData

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : FiniteMapData c ε)

theorem range_subset_V : Set.range ε.1.base ⊆ (𝔉.V : Set C) := by
  rintro x ⟨y, rfl⟩
  have hx : ε.1.base y ∈ (⊤ : C.Opens) := trivial
  rw [← 𝔉.sup_eq_top, TopologicalSpace.Opens.mem_sup] at hx
  rcases hx with h | h
  · exact absurd ⟨y, rfl⟩ ((𝔉.mem_U_iff _).mp h)
  · exact h

theorem coe_U_eq_compl : (𝔉.U : Set C) = (Set.range ε.1.base)ᶜ :=
  Set.ext fun x => 𝔉.mem_U_iff x

theorem isAffineOpen_inf : IsAffineOpen (𝔉.U ⊓ 𝔉.V) := by
  rw [𝔉.inf_eq_basicOpen]; exact 𝔉.isAffineOpen_U.basicOpen _

theorem basicOpen_f_eq_basicOpen_g : C.basicOpen 𝔉.f = C.basicOpen 𝔉.g := by
  rw [← 𝔉.inf_eq_basicOpen, 𝔉.inf_eq_basicOpen_g]

/-- The two-chart affine cover, ordered with the chart containing the section first. -/
def twoAffineOpenCover : C.TwoAffineOpenCover where
  U0 := 𝔉.V
  U1 := 𝔉.U
  isAffineOpen_U0 := 𝔉.isAffineOpen_V
  isAffineOpen_U1 := 𝔉.isAffineOpen_U
  sup_eq_top := by rw [sup_comm, 𝔉.sup_eq_top]
  isAffineOpen_inf := by rw [inf_comm]; exact 𝔉.isAffineOpen_inf

@[simp] theorem twoAffineOpenCover_U0 : 𝔉.twoAffineOpenCover.U0 = 𝔉.V := rfl
@[simp] theorem twoAffineOpenCover_U1 : 𝔉.twoAffineOpenCover.U1 = 𝔉.U := rfl

theorem range_subset_twoAffineOpenCover_U0 :
    Set.range ε.1.base ⊆ (𝔉.twoAffineOpenCover.U0 : Set C) :=
  𝔉.range_subset_V

theorem twoAffineOpenCover_U1_eq_compl :
    (𝔉.twoAffineOpenCover.U1 : Set C) = (Set.range ε.1.base)ᶜ :=
  𝔉.coe_U_eq_compl

theorem moduleFinite_U :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    letI : Algebra (Polynomial R) Γ(C, 𝔉.U) :=
      (Polynomial.aeval 𝔉.f : Polynomial R →ₐ[R] Γ(C, 𝔉.U)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.U) :=
  𝔉.finite_f

theorem moduleFinite_V :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.V
    letI : Algebra (Polynomial R) Γ(C, 𝔉.V) :=
      (Polynomial.aeval 𝔉.g : Polynomial R →ₐ[R] Γ(C, 𝔉.V)).toRingHom.toAlgebra
    Module.Finite (Polynomial R) Γ(C, 𝔉.V) :=
  𝔉.finite_g

theorem levelSet_finite (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.Finite S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) :=
  (𝔉.levelSet_free S s).1

theorem levelSet_finrank_eq (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
    Module.finrank S (S ⊗[R] Γ(C, 𝔉.U) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))}) = 𝔉.m :=
  (𝔉.levelSet_free S s).2.2

/-- A polynomial with a unit coefficient controls étaleness of the coordinate level sets. -/
def LevelSetsGenericallyEtale : Prop :=
  ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s : S),
      IsUnit (Polynomial.aeval s D) →
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
      Algebra.Etale S (S ⊗[R] Γ(C, 𝔉.U) ⧸
        Ideal.span {(1 : S) ⊗ₜ[R] 𝔉.f - s ⊗ₜ[R] (1 : Γ(C, 𝔉.U))})

end FiniteMapData

end AlgebraicGeometry.SmoothProperCurve

end
