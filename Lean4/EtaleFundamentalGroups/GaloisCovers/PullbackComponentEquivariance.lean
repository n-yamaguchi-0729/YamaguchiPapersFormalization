/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PullbackComponentQuotient

/-!
# Equivariance of the actual inclusion of a Galois pullback component

The homomorphism from the deck group of a pointed pullback component to the
original deck group is defined using the two pointed fundamental-group
quotients. This file proves that it intertwines the actual component inclusion
with the pulled-back deck transformations. The compatibility is derived from
surjectivity of the component quotient, naturality of the fiber comparison,
and injectivity of evaluation on morphisms out of a connected cover.

This supplies the deck-equivariance input for subsequent comparisons of
normalization geometric-point stabilizers. It does not identify those
stabilizers with mapped local ideal inertia: choosing and comparing the
normalization points is a separate geometric step.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- The actual inclusion of a pointed Galois pullback component intertwines
its deck transformations with the corresponding pulled-back original deck
transformations. No equivariance hypothesis is added. -/
theorem galoisPullbackComponentQuotientMonoidHom_equivariant
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (W : FiniteEtale Y) (hW : IsGalois W)
    (w : (fiber (xi ≫ f)).obj W)
    (Z : FiniteEtale X) (i : Z ⟶ (pullback f).obj W)
    (z : (fiber xi).obj Z)
    (hiz : (fiber xi).map i z =
      transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) W w)
    (hZ : IsGalois Z) (hi : Mono i)
    (sigma : (Aut Z)ᵐᵒᵖ) :
    sigma.unop.hom ≫ i =
      i ≫ (pullback f).map
        ((galoisPullbackComponentQuotientMonoidHom
          f xi W hW w Z i z hiz hZ hi sigma).unop.hom) := by
  let : IsGalois W := hW
  let : IsGalois Z := hZ
  let F := fiber (xi ≫ f)
  let F' := fiber xi
  let H := pullback f
  let t := pullbackFiberIso f xi
  let y : F'.obj (H.obj W) := transportedPointOfCompIso H t W w
  let qZ := finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
  let qW := Inertia.finiteEtaleGaloisCoverQuotientOfMorphism f xi W hW w
  let phi := galoisPullbackComponentQuotientMonoidHom f xi W hW w Z i z hiz hZ hi
  obtain ⟨gamma, rfl⟩ :=
    finiteEtaleGaloisCoverQuotientMonoidHom_surjective xi Z hZ z sigma
  have hphi : phi (qZ gamma) = qW gamma :=
    MonoidHom.ext_iff.mp
      (galoisPullbackComponentQuotientMonoidHom_comp
        f xi W hW w Z i z hiz hZ hi) gamma
  change (qZ gamma).unop.hom ≫ i = i ≫ H.map ((phi (qZ gamma)).unop.hom)
  rw [hphi]
  apply evaluation_injective_of_isConnected F' Z (H.obj W) z
  change F'.map ((qZ gamma).unop.hom ≫ i) z =
    F'.map (i ≫ H.map ((qW gamma).unop.hom)) z
  rw [Functor.map_comp, Functor.map_comp, FintypeCat.comp_apply,
    FintypeCat.comp_apply]
  have hcomponent : F'.map ((qZ gamma).unop.hom) z = gamma • z :=
    finiteEtaleGaloisCoverQuotientMonoidHom_evaluation xi Z hZ z gamma
  rw [hcomponent, ← mulAction_naturality, hiz]
  change gamma • y = F'.map (H.map ((qW gamma).unop.hom)) y
  have hquotient : F.map ((qW gamma).unop.hom) w =
      (fundamentalGroupHom f xi gamma) • w :=
    finiteEtaleGaloisCoverQuotientMonoidHom_evaluation
      (xi ≫ f) W hW w (fundamentalGroupHom f xi gamma)
  have haction : (t.inv.app W) ((fundamentalGroupHom f xi gamma) • w) =
      gamma • y := by
    change (t.inv.app W) ((t.hom.app W)
      (gamma.hom.app (H.obj W) ((t.inv.app W) w))) =
        gamma.hom.app (H.obj W) ((t.inv.app W) w)
    exact FintypeCat.hom_inv_id_apply (t.app W) _
  have hnat := ConcreteCategory.congr_hom
    (t.inv.naturality ((qW gamma).unop.hom)) w
  change (t.inv.app W) (F.map ((qW gamma).unop.hom) w) =
    F'.map (H.map ((qW gamma).unop.hom)) y at hnat
  rw [hquotient, haction] at hnat
  exact hnat

end AlgebraicGeometry.FiniteEtale
