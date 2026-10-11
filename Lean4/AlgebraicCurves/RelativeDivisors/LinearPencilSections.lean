/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Modules.PullbackLocalSection
import SchemeTheory.Modules.PullbackUnitComposition
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Actual sections in a linear pencil

The section `(1-t)s₀ + ts₁` is formed on the actual product with the affine
line. Its restrictions along the sections `t = a` are computed through the
canonical composition and identity isomorphisms for pullback of modules.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.LinearPencil

open Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The structure morphism of the affine parameter line. -/
def lineMap : Spec (CommRingCat.of (Polynomial R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- Evaluation at a base-ring element, as a section of the affine line. -/
def evaluate (a : R) : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))

theorem evaluate_comp_lineMap (a : R) : evaluate a ≫ lineMap = 𝟙 _ := by
  rw [evaluate, lineMap, ← Spec.map_comp]
  have h : CommRingCat.ofHom Polynomial.C ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of R) := by
    ext r
    exact Polynomial.eval_C
  rw [h, Spec.map_id]

variable (c : X ⟶ Spec (CommRingCat.of R))

/-- Inclusion of the fibre with parameter `a` into the actual product. -/
def fibre (a : R) : X ⟶ pullback c lineMap :=
  pullback.lift (𝟙 X) (c ≫ evaluate a) (by
    rw [Category.id_comp, Category.assoc, evaluate_comp_lineMap, Category.comp_id])

theorem fibre_fst (a : R) : fibre c a ≫ pullback.fst c lineMap = 𝟙 X :=
  pullback.lift_fst _ _ _

theorem fibre_snd (a : R) : fibre c a ≫ pullback.snd c lineMap = c ≫ evaluate a :=
  pullback.lift_snd _ _ _

/-- The actual parameter as a global function on the product. -/
def parameter : Γ(pullback c lineMap, ⊤) :=
  (pullback.snd c lineMap).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv Polynomial.X)

theorem parameter_fibre (a : R) : (fibre c a).appTop (parameter c) =
    c.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
  have hn := congrArg (fun k => k ((Scheme.ΓSpecIso
      (CommRingCat.of (Polynomial R))).inv Polynomial.X))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Polynomial.evalRingHom a)))
  have he : (evaluate a).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial R))).inv Polynomial.X) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv a := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
    simpa only [evaluate, CategoryTheory.comp_apply, Iso.inv_hom_id_apply,
      CommRingCat.hom_ofHom, Polynomial.coe_evalRingHom, Polynomial.eval_X] using hn
  change ((pullback.snd c lineMap).appTop ≫ (fibre c a).appTop) _ = _
  rw [← Scheme.Hom.comp_appTop, fibre_snd, Scheme.Hom.comp_appTop]
  exact congrArg c.appTop he

private theorem pullbackComp_section {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    (g : Y ⟶ X) (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackComp f g).hom.app M).app ⊤
      (pullbackLocalSection f (pullbackLocalSection g s)) =
      pullbackLocalSection (f ≫ g) s := by
  have h := congrArg (fun k => k s) (unit_app_comp_pullbackComp_inv f g M ⊤)
  change ((pullbackComp f g).inv.app M).app ⊤
    (pullbackLocalSection (f ≫ g) s) =
    pullbackLocalSection f (pullbackLocalSection g s) at h
  rw [← h]
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (pullbackLocalSection (f ≫ g) s)) ((pullbackComp f g).inv_hom_id_app M)

private theorem pullbackId_section (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackId X).hom.app M).app ⊤ (pullbackLocalSection (𝟙 X) s) = s := by
  have h := unit_conjugateEquiv Adjunction.id
    (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at h
  have hh := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s) h
  exact hh.symm

private theorem pullbackCongr_section {Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackCongr h).hom.app M).app ⊤ (pullbackLocalSection f s) =
      pullbackLocalSection g s := by
  subst g
  exact congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (pullbackLocalSection f s)) (show (pullbackCongr rfl).hom.app M = 𝟙 _ from rfl)

/-- Canonical comparison of a pulled-back module with its restriction to a fibre. -/
def fibreModuleIso (a : R) (M : X.Modules) :
    (Scheme.Modules.pullback (fibre c a)).obj
      ((Scheme.Modules.pullback (pullback.fst c lineMap)).obj M) ≅ M :=
  (pullbackComp (fibre c a) (pullback.fst c lineMap)).app M ≪≫
    (pullbackCongr (fibre_fst c a)).app M ≪≫ (pullbackId X).app M

theorem fibreModuleIso_section (a : R) (M : X.Modules) (s : Γ(M, ⊤)) :
    (fibreModuleIso c a M).hom.app ⊤
      (pullbackLocalSection (fibre c a)
        (pullbackLocalSection (pullback.fst c lineMap) s)) = s := by
  change ((pullbackId X).hom.app M).app ⊤
    (((pullbackCongr (fibre_fst c a)).hom.app M).app ⊤
      (((pullbackComp (fibre c a) (pullback.fst c lineMap)).hom.app M).app ⊤
        (pullbackLocalSection (fibre c a)
          (pullbackLocalSection (pullback.fst c lineMap) s)))) = s
  rw [pullbackComp_section, pullbackCongr_section, pullbackId_section]

/-- Linear interpolation of two sections on the actual affine-line product. -/
def pencilSection (M : X.Modules) (s₀ s₁ : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback (pullback.fst c lineMap)).obj M, ⊤) :=
  let N : (pullback c lineMap).Modules :=
    (Scheme.Modules.pullback (pullback.fst c lineMap)).obj M
  let v₀ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₀
  let v₁ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₁
  let w₀ : Γ(N, ⊤) := (1 - parameter c) • v₀
  let w₁ : Γ(N, ⊤) := parameter c • v₁
  w₀ + w₁

/-- Pullback of the actual pencil along an arbitrary test-scheme morphism.
This includes geometric fibres over extensions of the ground field. -/
theorem pencilSection_pullback {Y : Scheme.{u}} (φ : Y ⟶ pullback c lineMap)
    (M : X.Modules) (s₀ s₁ : Γ(M, ⊤)) :
    let V : Y.Modules := (Scheme.Modules.pullback (φ ≫ pullback.fst c lineMap)).obj M
    let v₀ : Γ(V, ⊤) := pullbackLocalSection (φ ≫ pullback.fst c lineMap) s₀
    let v₁ : Γ(V, ⊤) := pullbackLocalSection (φ ≫ pullback.fst c lineMap) s₁
    ((pullbackComp φ (pullback.fst c lineMap)).hom.app M).app ⊤
      (pullbackLocalSection φ (pencilSection c M s₀ s₁)) =
      (1 - φ.appTop (parameter c)) • v₀ + φ.appTop (parameter c) • v₁ := by
  intro V v₀ v₁
  let N : (pullback c lineMap).Modules :=
    (Scheme.Modules.pullback (pullback.fst c lineMap)).obj M
  let z₀ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₀
  let z₁ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₁
  let W : Y.Modules := (Scheme.Modules.pullback φ).obj N
  let w₀ : Γ(W, ⊤) := pullbackLocalSection φ z₀
  let w₁ : Γ(W, ⊤) := pullbackLocalSection φ z₁
  have h₀ : ((pullbackComp φ (pullback.fst c lineMap)).hom.app M).app ⊤ w₀ = v₀ :=
    pullbackComp_section φ (pullback.fst c lineMap) M s₀
  have h₁ : ((pullbackComp φ (pullback.fst c lineMap)).hom.app M).app ⊤ w₁ = v₁ :=
    pullbackComp_section φ (pullback.fst c lineMap) M s₁
  change ((pullbackComp φ (pullback.fst c lineMap)).hom.app M).app ⊤
    (pullbackLocalSection φ ((1 - parameter c) • z₀ + parameter c • z₁)) = _
  rw [pullbackLocalSection_add, pullbackLocalSection_smul (L := N) (U := ⊤),
    pullbackLocalSection_smul (L := N) (U := ⊤)]
  change ((pullbackComp φ (pullback.fst c lineMap)).hom.app M).app ⊤
    ((φ.appTop (1 - parameter c)) • w₀ + φ.appTop (parameter c) • w₁) = _
  rw [map_sub, map_one, map_add, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.Hom.app_smul, h₀, h₁]

/-- Restricting the actual pencil to `t=a` gives the stated linear combination. -/
theorem section_fibre (a : R) (M : X.Modules) (s₀ s₁ : Γ(M, ⊤)) :
    (fibreModuleIso c a M).hom.app ⊤
      (pullbackLocalSection (fibre c a) (pencilSection c M s₀ s₁)) =
      (1 - c.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) • s₀ +
        c.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) • s₁ := by
  let N : (pullback c lineMap).Modules :=
    (Scheme.Modules.pullback (pullback.fst c lineMap)).obj M
  let v₀ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₀
  let v₁ : Γ(N, ⊤) := pullbackLocalSection (pullback.fst c lineMap) s₁
  let W : X.Modules := (Scheme.Modules.pullback (fibre c a)).obj N
  let w₀ : Γ(W, ⊤) := pullbackLocalSection (fibre c a) v₀
  let w₁ : Γ(W, ⊤) := pullbackLocalSection (fibre c a) v₁
  have h₀ : (fibreModuleIso c a M).hom.app ⊤
      w₀ = s₀ := fibreModuleIso_section c a M s₀
  have h₁ : (fibreModuleIso c a M).hom.app ⊤
      w₁ = s₁ := fibreModuleIso_section c a M s₁
  change (fibreModuleIso c a M).hom.app ⊤
    (pullbackLocalSection (fibre c a) ((1 - parameter c) • v₀ + parameter c • v₁)) = _
  rw [pullbackLocalSection_add, pullbackLocalSection_smul (L := N) (U := ⊤),
    pullbackLocalSection_smul (L := N) (U := ⊤)]
  change (fibreModuleIso c a M).hom.app ⊤
    (((fibre c a).appTop (1 - parameter c)) • w₀ +
      (fibre c a).appTop (parameter c) • w₁) = _
  rw [map_sub, map_one, parameter_fibre]
  rw [map_add, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h₀, h₁]

end AlgebraicGeometry.LinearPencil
