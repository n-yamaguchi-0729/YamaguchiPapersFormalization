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

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.AbelianSchemePropertyBundle

/-!
# Pointed carriers for the relative Picard construction

A relative Picard designation records a scheme over the base with a chosen zero section.
The avatar bridge identifies an additive group with its points over a test scheme and
records compatibility with the relative group law.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

/-- A chosen scheme over the base, equipped with a zero section. -/
structure RelativePic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) where
  /-- The scheme designated as the relative Picard carrier. -/
  P : Scheme.{u}
  /-- The structure morphism to the base scheme. -/
  toBase : P ⟶ Spec (CommRingCat.of R)
  /-- The chosen zero section of the structure morphism. -/
  zeroSection : Spec (CommRingCat.of R) ⟶ P
  /-- The zero section is a section of `toBase`. -/
  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

/-- The designation whose carrier is the base itself and whose maps are identities. -/
def trivialPic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    RelativePic0Designation R c where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

end AbstractCarriers

section AvatarBridge

variable {R : Type u} [CommRing R]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

/-- An identification of an additive group with scheme points compatible with the group law. -/
structure AvatarSchemeBridge (A : Type*) [AddCommGroup A]
    (D : RelativePic0Designation R c) (L : RelativeGroupLaw R D.toBase)
    {T : Scheme.{u}} (σ : T ⟶ Spec (CommRingCat.of R)) where
  /-- The equivalence from the additive group to points over the test scheme. -/
  pts : A ≃ SchemeHomOver σ D.toBase
  /-- Addition of avatar elements corresponds to multiplication in the relative group law. -/
  pts_add : ∀ x y : A, pts (x + y) = L.mul σ (pts x) (pts y)
  /-- The zero avatar point is induced by the designated zero section. -/
  pts_zero : (pts 0).1 = σ ≫ D.zeroSection

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}

theorem law_one_eq_pts_zero (B : AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 := by
  have hidem : L.mul σ (B.pts 0) (B.pts 0) = B.pts 0 := by
    rw [← B.pts_add, add_zero]
  calc L.one σ
      = L.mul σ (L.inv σ (B.pts 0)) (B.pts 0) := (L.inv_mul_cancel σ (B.pts 0)).symm
    _ = L.mul σ (L.inv σ (B.pts 0)) (L.mul σ (B.pts 0) (B.pts 0)) := by rw [hidem]
    _ = L.mul σ (L.mul σ (L.inv σ (B.pts 0)) (B.pts 0)) (B.pts 0) :=
        (L.mul_assoc σ _ _ _).symm
    _ = L.mul σ (L.one σ) (B.pts 0) := by rw [L.inv_mul_cancel]
    _ = B.pts 0 := L.one_mul σ _

end AvatarSchemeBridge

end AvatarBridge

end GoodReductionJacobian
