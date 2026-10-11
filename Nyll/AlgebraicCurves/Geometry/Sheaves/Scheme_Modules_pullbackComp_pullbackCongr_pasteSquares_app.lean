/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
Compare pullback composition isomorphisms along pasted commutative squares on sheaves of
modules.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X₀ X₁ X₂ X₃ : Scheme.{u}}

theorem pullbackComp_paste (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    Functor.whiskerLeft (Modules.pullback h) (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight (pullbackComp g h).hom
        (Modules.pullback f) ≫
        (pullbackComp f (g ≫ h)).hom ≫ eqToHom (by rw [Category.assoc]) := by
  have H0 := pseudofunctor_associativity f g h
  have H1 : Functor.whiskerLeft (Modules.pullback h) (pullbackComp f g).hom ≫ (pullbackComp (f ≫
    g) h).hom =
      (Functor.associator _ _ _).inv ≫ (Functor.isoWhiskerRight (pullbackComp g h)
        (Modules.pullback f)).hom ≫
        (pullbackComp f (g ≫ h)).hom ≫
        ((pullbackComp f (g ≫ h)).inv ≫ Functor.whiskerRight (pullbackComp g h).inv
          (Modules.pullback f) ≫
          (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (Modules.pullback h)
            (pullbackComp f g).hom ≫
            (pullbackComp (f ≫ g) h).hom) := by
    rw [Iso.hom_inv_id_assoc, Functor.isoWhiskerRight_hom, ← Functor.whiskerRight_comp_assoc,
      Iso.hom_inv_id,
      Functor.whiskerRight_id', Category.id_comp, Iso.inv_hom_id_assoc]
  rw [H0] at H1
  exact H1

theorem pullbackComp_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (M : X₃.Modules) :
    (pullbackComp f g).hom.app ((Modules.pullback h).obj M) ≫ (pullbackComp (f ≫ g) h).hom.app M =
      (Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫ (pullbackComp f (g ≫ h)).hom.app M ≫
        eqToHom (by rw [Category.assoc]) := by
  have H := NatTrans.congr_app (pullbackComp_paste f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app,
    eqToHom_app] at H
  exact H

/-- The isomorphism from successive pullbacks along `g` and `f` to pullback along `m` determined
by `e`. -/
noncomputable def τ (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) : Modules.pullback
    g ⋙ Modules.pullback f ≅ Modules.pullback m :=
  pullbackComp f g ≪≫ pullbackCongr e

theorem τ_hom_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).hom.app M = (pullbackComp f g).hom.app M ≫ eqToHom (by rw [e]) := by
  subst e
  simp [τ, pullbackCongr]

theorem τ_paste_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (fg : X₀ ⟶ X₂) (gh : X₁ ⟶ X₃) (m :
    X₀ ⟶ X₃)
    (e₁ : f ≫ g = fg) (e₂ : g ≫ h = gh) (e₃ : fg ≫ h = m) (M : X₃.Modules) :
    (τ f g fg e₁).hom.app ((Modules.pullback h).obj M) ≫ (τ fg h m e₃).hom.app M =
      (Modules.pullback f).map ((τ g h gh e₂).hom.app M) ≫ (τ f gh m (by rw [← e₂, ←
        Category.assoc, e₁, e₃])).hom.app M := by
  subst e₁ e₂ e₃
  simp only [τ_hom_app, eqToHom_refl, Category.comp_id]
  rw [pullbackComp_paste_app]

theorem τ_inv_app (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (m : X₀ ⟶ X₂) (e : f ≫ g = m) (M : X₂.Modules) :
    (τ f g m e).inv.app M = eqToHom (by rw [e]) ≫ (pullbackComp f g).inv.app M := by
  subst e
  simp [τ, pullbackCongr]

/-- The isomorphism between the two iterated pullback functors in the commutative square `e`. -/
noncomputable def sqIso {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) : Modules.pullback g ⋙ Modules.pullback f ≅ Modules.pullback k ⋙
      Modules.pullback h :=
  pullbackComp f g ≪≫ pullbackCongr e ≪≫ (pullbackComp h k).symm

theorem sqIso_hom_app {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) :
    (sqIso e).hom.app M = (τ f g (h ≫ k) e).hom.app M ≫ (τ h k (h ≫ k) rfl).inv.app M := by
  simp [sqIso, τ, pullbackCongr]

theorem map_sqIso_hom_app {W X Y Z V : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {h : W ⟶ Y} {k : Y ⟶ Z}
    (e : f ≫ g = h ≫ k) (M : Z.Modules) (G : W.Modules ⥤ V.Modules) :
    G.map ((sqIso e).hom.app M) =
      G.map ((τ f g (h ≫ k) e).hom.app M) ≫ G.map ((τ h k (h ≫ k) rfl).inv.app M) := by
  rw [sqIso_hom_app, G.map_comp]

private theorem route_composition {C : Type*} [Category C]
    {A B C₀ D E F G H : C}
    (α : A ⟶ F) (β : B ≅ F) (γ : B ⟶ G) (δ : C₀ ≅ G) (ε : C₀ ⟶ D)
    (ζ : F ⟶ H) (η : G ⟶ H) (θ : D ≅ H) (κ : A ⟶ E) (ℓ : E ⟶ H)
    (h₁ : β.hom ≫ ζ = γ ≫ η) (h₂ : ε ≫ θ.hom = δ.hom ≫ η)
    (h₃ : α ≫ ζ = κ ≫ ℓ) :
    (α ≫ β.inv) ≫ (γ ≫ δ.inv) ≫ ε = κ ≫ ℓ ≫ θ.inv := by
  apply (cancel_mono θ.hom).1
  calc
    ((α ≫ β.inv) ≫ (γ ≫ δ.inv) ≫ ε) ≫ θ.hom =
        α ≫ β.inv ≫ γ ≫ δ.inv ≫ (ε ≫ θ.hom) := by
      simp only [Category.assoc]
    _ = α ≫ β.inv ≫ γ ≫ δ.inv ≫ (δ.hom ≫ η) := by rw [h₂]
    _ = α ≫ β.inv ≫ (γ ≫ η) := by rw [Iso.inv_hom_id_assoc]
    _ = α ≫ β.inv ≫ (β.hom ≫ ζ) := by rw [← h₁]
    _ = α ≫ ζ := by rw [Iso.inv_hom_id_assoc]
    _ = κ ≫ ℓ := h₃
    _ = (κ ≫ ℓ ≫ θ.inv) ≫ θ.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

section Route

variable {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
  (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
  (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
  (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s)

include e G E F in
theorem route_comm : s₀ ≫ d = m ≫ s := by
  rw [← e, ← Category.assoc, E, Category.assoc, F, ← Category.assoc, G]

theorem route (M : X.Modules) :
    (sqIso E).hom.app ((Modules.pullback b).obj M) ≫ (Modules.pullback r).map ((sqIso F).hom.app
      M) ≫
        (τ r p m G).hom.app ((Modules.pullback s).obj M) =
      (Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫
        (τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M ≫
          (τ m s (m ≫ s) rfl).inv.app M := by
  have hn : (r ≫ s₁) ≫ b = m ≫ s := by rw [Category.assoc, F, ← Category.assoc, G]
  have P1 := τ_paste_app r s₁ b (r ≫ s₁) (p ≫ s) (m ≫ s) rfl F hn M
  have P2 := τ_paste_app r p s m (p ≫ s) (m ≫ s) G rfl rfl M
  have P3 := τ_paste_app s₀ a b (r ≫ s₁) d (m ≫ s) E e hn M
  rw [sqIso_hom_app (e := E), map_sqIso_hom_app (e := F)]
  exact route_composition
    ((τ s₀ a (r ≫ s₁) E).hom.app ((Modules.pullback b).obj M))
    ((τ r s₁ (r ≫ s₁) rfl).app ((Modules.pullback b).obj M))
    ((Modules.pullback r).map ((τ s₁ b (p ≫ s) F).hom.app M))
    ((Modules.pullback r).mapIso ((τ p s (p ≫ s) rfl).app M))
    ((τ r p m G).hom.app ((Modules.pullback s).obj M))
    ((τ (r ≫ s₁) b (m ≫ s) hn).hom.app M)
    ((τ r (p ≫ s) (m ≫ s) (by rw [← Category.assoc, G])).hom.app M)
    ((τ m s (m ≫ s) rfl).app M)
    ((Modules.pullback s₀).map ((τ a b d e).hom.app M))
    ((τ s₀ d (m ≫ s) (route_comm a b d e s₀ s₁ s r p m G E F)).hom.app M)
    P1 P2 P3

end Route

section Head

variable {X X₀' X₁' X₂' Y Y₀ Y₁ Y₂ : Scheme.{u}}
  (a₁ : X₀' ⟶ X₁') (b₁ : X₁' ⟶ X) (a₂ : X₀' ⟶ X₂') (b₂ : X₂' ⟶ X) (d : X₀' ⟶ X)
  (e₁ : a₁ ≫ b₁ = d) (e₂ : a₂ ≫ b₂ = d)
  (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s₂ : Y₂ ⟶ X₂') (s : Y ⟶ X)
  (r₁ : Y₀ ⟶ Y₁) (p₁ : Y₁ ⟶ Y) (r₂ : Y₀ ⟶ Y₂) (p₂ : Y₂ ⟶ Y) (m : Y₀ ⟶ Y)
  (G₁ : r₁ ≫ p₁ = m) (G₂ : r₂ ≫ p₂ = m)
  (E₁ : s₀ ≫ a₁ = r₁ ≫ s₁) (F₁ : s₁ ≫ b₁ = p₁ ≫ s) (E₂ : s₀ ≫ a₂ = r₂ ≫ s₂) (F₂ : s₂ ≫ b₂ = p₂ ≫ s)

theorem head (M : X.Modules) :
    (Modules.pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M ≫ (τ a₂ b₂ d e₂).inv.app M) ≫
      (sqIso E₂).hom.app ((Modules.pullback b₂).obj M) ≫ (Modules.pullback r₂).map ((sqIso
        F₂).hom.app M) ≫
        (τ r₂ p₂ m G₂).hom.app ((Modules.pullback s).obj M) =
      (sqIso E₁).hom.app ((Modules.pullback b₁).obj M) ≫ (Modules.pullback r₁).map ((sqIso
        F₁).hom.app M) ≫
        (τ r₁ p₁ m G₁).hom.app ((Modules.pullback s).obj M) := by
  have h₁ := route a₁ b₁ d e₁ s₀ s₁ s r₁ p₁ m G₁ E₁ F₁ M
  have h₂ := route a₂ b₂ d e₂ s₀ s₂ s r₂ p₂ m G₂ E₂ F₂ M
  have h₂' := (Iso.inv_comp_eq ((Modules.pullback s₀).mapIso ((τ a₂ b₂ d e₂).app M))).mpr h₂
  simp only [Functor.map_comp, Category.assoc]
  exact (congrArg (fun k => (Modules.pullback s₀).map ((τ a₁ b₁ d e₁).hom.app M) ≫ k) h₂').trans
    h₁.symm

end Head

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

theorem route' {X X₀' X₁' Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀' ⟶ X₁') (b : X₁' ⟶ X) (d : X₀' ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀') (s₁ : Y₁ ⟶ X₁') (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (sqIso E).hom.app ((Modules.pullback b).obj M) ≫ (Modules.pullback r).map ((sqIso F).hom.app
      M) ≫
        (τ r p m G).hom.app ((Modules.pullback s).obj M) =
      (Modules.pullback s₀).map ((τ a b d e).hom.app M) ≫ (sqIso H).hom.app M := by
  rw [sqIso_hom_app (e := H)]
  exact route a b d e s₀ s₁ s r p m G E F M

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    {X X₀ X₁ Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X) (d : X₀ ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀) (s₁ : Y₁ ⟶ X₁) (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (Scheme.Modules.pullbackComp s₀ a ≪≫ Scheme.Modules.pullbackCongr E ≪≫
          (Scheme.Modules.pullbackComp r s₁).symm).hom.app ((Scheme.Modules.pullback b).obj M) ≫
      (Scheme.Modules.pullback r).map
          ((Scheme.Modules.pullbackComp s₁ b ≪≫ Scheme.Modules.pullbackCongr F ≪≫
            (Scheme.Modules.pullbackComp p s).symm).hom.app M) ≫
        (Scheme.Modules.pullbackComp r p ≪≫ Scheme.Modules.pullbackCongr G).hom.app
          ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map
          ((Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp s₀ d ≪≫ Scheme.Modules.pullbackCongr H ≪≫
          (Scheme.Modules.pullbackComp m s).symm).hom.app M :=
  AlgebraicGeometry.Scheme.Modules.route' a b d e s₀ s₁ s r p m G E F H M
end Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
