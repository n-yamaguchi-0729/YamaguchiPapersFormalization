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

import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Scheme morphisms over a fixed base

Scheme morphisms compatible with chosen structure morphisms form a subtype. This file
constructs their identities, composition, and actions on points, and identifies them with
morphisms in the over category. It also records existence and uniqueness over an isomorphism.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace NeronModelInfra

/-- Scheme morphisms commuting with the specified structure morphisms to the base. -/
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  {φ : Y ⟶ X // φ ≫ f = g}

variable {B Y X W : Scheme.{u}}

/-- The identity scheme morphism over the base. -/
def schemeHomOverId (f : X ⟶ B) : SchemeHomOver f f :=
  ⟨𝟙 X, Category.id_comp f⟩
@[simp]
theorem schemeHomOverId_coe (f : X ⟶ B) : (schemeHomOverId f).1 = 𝟙 X :=
  rfl

/-- Composition of two scheme morphisms over the base. -/
def schemeHomOverComp {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) : SchemeHomOver g e :=
  ⟨φ.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, φ.2]⟩
@[simp]
theorem schemeHomOverComp_coe {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) :
    (schemeHomOverComp φ ψ).1 = φ.1 ≫ ψ.1 :=
  rfl

/-- Postcomposition of a base-valued point by a scheme morphism over the base. -/
def mapPt {T A A' : Scheme.{u}} {t : T ⟶ B} {f : A ⟶ B} {f' : A' ⟶ B}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
@[simp]
theorem mapPt_coe {T A A' : Scheme.{u}} {t : T ⟶ B} {f : A ⟶ B} {f' : A' ⟶ B}
    (φ : A ⟶ A') (hφ : φ ≫ f' = f) (P : SchemeHomOver t f) :
    (mapPt φ hφ P).1 = P.1 ≫ φ :=
  rfl

theorem schemeHomOverComp_assoc {V : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B} {e : W ⟶ B}
    {d : V ⟶ B} (φ : SchemeHomOver g f) (ψ : SchemeHomOver f e) (χ : SchemeHomOver e d) :
    schemeHomOverComp (schemeHomOverComp φ ψ) χ =
      schemeHomOverComp φ (schemeHomOverComp ψ χ) := by
  apply Subtype.ext
  exact Category.assoc φ.1 ψ.1 χ.1
@[simp]
theorem schemeHomOverComp_id_left {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp (schemeHomOverId g) φ = φ := by
  apply Subtype.ext
  exact Category.id_comp φ.1
@[simp]
theorem schemeHomOverComp_id_right {g : Y ⟶ B} {f : X ⟶ B} (φ : SchemeHomOver g f) :
    schemeHomOverComp φ (schemeHomOverId f) = φ := by
  apply Subtype.ext
  exact Category.comp_id φ.1

/-- The over-category morphism associated to a scheme morphism over the base. -/
def schemeHomOverToOverHom {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : Over.mk g ⟶ Over.mk f :=
  Over.homMk φ.1 φ.2
@[simp]
theorem schemeHomOverToOverHom_left {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : (schemeHomOverToOverHom φ).left = φ.1 :=
  rfl

/-- The scheme morphism over the base underlying an over-category morphism. -/
def overHomToSchemeHomOver {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : SchemeHomOver g f :=
  ⟨h.left, Over.w h⟩
@[simp]
theorem overHomToSchemeHomOver_coe {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : (overHomToSchemeHomOver h).1 = h.left :=
  rfl
@[simp]
theorem overHomToSchemeHomOver_schemeHomOverToOverHom {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : overHomToSchemeHomOver (schemeHomOverToOverHom φ) = φ :=
  Subtype.ext
    ((overHomToSchemeHomOver_coe (schemeHomOverToOverHom φ)).trans
      (schemeHomOverToOverHom_left φ))
@[simp]
theorem schemeHomOverToOverHom_overHomToSchemeHomOver {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : schemeHomOverToOverHom (overHomToSchemeHomOver h) = h :=
  Over.OverMorphism.ext
    ((schemeHomOverToOverHom_left (overHomToSchemeHomOver h)).trans
      (overHomToSchemeHomOver_coe h))

/-- The equivalence between scheme morphisms over the base and over-category morphisms. -/
def schemeHomOverEquivOverHom (g : Y ⟶ B) (f : X ⟶ B) :
    SchemeHomOver g f ≃ (Over.mk g ⟶ Over.mk f) where
  toFun := schemeHomOverToOverHom
  invFun := overHomToSchemeHomOver
  left_inv := overHomToSchemeHomOver_schemeHomOverToOverHom
  right_inv := schemeHomOverToOverHom_overHomToSchemeHomOver
@[simp]
theorem schemeHomOverEquivOverHom_apply {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : schemeHomOverEquivOverHom g f φ = schemeHomOverToOverHom φ :=
  rfl
@[simp]
theorem schemeHomOverEquivOverHom_symm_apply {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) :
    (schemeHomOverEquivOverHom g f).symm h = overHomToSchemeHomOver h :=
  rfl

theorem subsingleton_schemeHomOver_of_isIso (g : Y ⟶ B) (f : X ⟶ B)
    [IsIso f] : Subsingleton (SchemeHomOver g f) := by
  constructor
  intro a b
  apply Subtype.ext
  have ha : a.1 = g ≫ inv f := by
    have h0 : a.1 = (a.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [a.2] at h0
    exact h0
  have hb : b.1 = g ≫ inv f := by
    have h0 : b.1 = (b.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [b.2] at h0
    exact h0
  rw [ha, hb]

theorem nonempty_schemeHomOver_of_isIso (g : Y ⟶ B) (f : X ⟶ B)
    [IsIso f] : Nonempty (SchemeHomOver g f) :=
  ⟨⟨g ≫ inv f, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

end NeronModelInfra

namespace GoodReductionJacobian

open NeronModelInfra

/-- Precomposition of a base-valued point by a scheme morphism over the base. -/
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl

end GoodReductionJacobian
