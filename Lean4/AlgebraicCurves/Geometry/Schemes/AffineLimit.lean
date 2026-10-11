/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_AffineLimit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Scheme

/-!
Relative affine spectra and finite-subalgebra descent and equality-detection conditions.
-/

universe w u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffineLimit

variable (R : Type u) [CommRing R]

/-- The affine spectrum of an R-algebra, viewed as an object over Spec R. -/
noncomputable abbrev specOver (A : Type u) [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The morphism of relative affine spectra induced by a subalgebra inclusion. -/
noncomputable abbrev specOverOfSubalgebra {A : Type u} [CommRing A] [Algebra R A]
    (A₀ : Subalgebra R A) :
    specOver R A ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

/-- The morphism of relative affine spectra induced by an inclusion of two subalgebras. -/
noncomputable abbrev specOverOfLE {A : Type u} [CommRing A] [Algebra R A]
    (A₀ A₁ : Subalgebra R A) (h : A₀ ≤ A₁) :
    specOver R A₁ ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

variable {R}

/-- Every functor-valued point descends to a finitely generated subalgebra. -/
def IsLFPSurj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (x : G.obj (op (specOver R A))),
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (x₀ : G.obj (op (specOver R A₀))),
      G.map (specOverOfSubalgebra R A₀).op x₀ = x

/-- Equality of functor-valued points is detected at a larger finitely generated subalgebra. -/
def IsLFPInj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
    (x₀ x₀' : G.obj (op (specOver R A₀))),
    G.map (specOverOfSubalgebra R A₀).op x₀ = G.map (specOverOfSubalgebra R A₀).op x₀' →
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
      G.map (specOverOfLE R A₀ A₁ h).op x₀ = G.map (specOverOfLE R A₀ A₁ h).op x₀'

/-- Finite-subalgebra descent and equality detection for a morphism to an affine spectrum. -/
def HomIsLFP {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) ∧
  (∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
      (φ₀ φ₀' : Spec (CommRingCat.of A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      φ₀' ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ =
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀' →
      ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀ =
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀')

end AlgebraicGeometry.AffineLimit
