/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.DeckOverComparison
import EtaleFundamentalGroups.GaloisCategories.PointedDeckTransport
import EtaleFundamentalGroups.GaloisCategories.AutFunctorComparison

/-!
# Actual geometric deck maps and subgroup conjugation

The deck pullback here is the scheme-theoretic pullback functor. Its pointed
fiber comparison is obtained from the actual over-category comparison and
ambient monodromy. Under the canonical inclusion of the covering fundamental
group, the induced automorphism is ambient conjugation.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} [ConnectedSpace S] (A : FiniteEtale S)
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]
variable (xi : Spec (.of Ω) ⟶ A.left)
local instance baseFiberFunctor : FiberFunctor (fiber (xi ≫ A.hom)) :=
  fiberFunctor (X := S) (xi ≫ A.hom)

variable (σ : Aut A) (g : π₁ᵉᵗ(xi ≫ A.hom))
variable (h : (fiber (xi ≫ A.hom)).map σ.hom (liftedFiberPoint A xi) =
  g • liftedFiberPoint A xi)

/-- A fiber comparison for the actual geometric pullback along a deck
automorphism, pointed by its lift in the ambient fundamental group. -/
def deckPointedGeometricFiberIso :
    pullback σ.hom.left ⋙ fiber xi ≅ fiber xi :=
  transportedEndofunctorFiberIso (overEquiv A).functor
    (pullback σ.hom.left) (Over.map σ.inv)
    (overEquivFiberIso A xi) (deckPullbackOverIso A σ)
    (pointedDeckFiberIso (fiber (xi ≫ A.hom))
      (liftedFiberPoint A xi) σ g h)

private theorem coverHom_autFiberOver (b : Aut
    (fiberOver (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi))) :
    fundamentalGroupHom A.hom xi (autFiberOverEquivFiber A xi b) =
      extendFiberOverAut (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi) b := by
  rw [← fundamentalGroupEquivStabilizerOfLift_coe A xi]
  change extendFiberOverAut (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi)
    ((autFiberOverEquivFiber A xi).symm (autFiberOverEquivFiber A xi b)) = _
  rw [(autFiberOverEquivFiber A xi).symm_apply_apply]

/-- The actual deck pullback induces conjugation on the actual covering
fundamental group, after its canonical inclusion in the base group. -/
theorem fundamentalGroupHom_deckPointed
    (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupHom A.hom xi
        (autHomOfCompIso (pullback σ.hom.left)
          (deckPointedGeometricFiberIso A xi σ g h) a) =
      g⁻¹ * fundamentalGroupHom A.hom xi a * g := by
  let b := (autFiberOverEquivFiber A xi).symm a
  have hb : autFiberOverEquivFiber A xi b = a :=
    (autFiberOverEquivFiber A xi).apply_symm_apply a
  have ht := autHomOfCompIso_transportedEndofunctor
    (overEquiv A).functor (pullback σ.hom.left) (Over.map σ.inv)
    (overEquivFiberIso A xi) (deckPullbackOverIso A σ)
    (pointedDeckFiberIso (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi) σ g h) b
  change autHomOfCompIso (pullback σ.hom.left)
      (deckPointedGeometricFiberIso A xi σ g h) (autFiberOverEquivFiber A xi b) =
    autFiberOverEquivFiber A xi
      (autHomOfCompIso (Over.map σ.inv)
        (pointedDeckFiberIso (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi) σ g h) b)
    at ht
  rw [hb] at ht
  rw [ht, coverHom_autFiberOver A xi]
  have he : extendFiberOverAut (fiber (xi ≫ A.hom)) (liftedFiberPoint A xi) b =
      fundamentalGroupHom A.hom xi a :=
    (coverHom_autFiberOver A xi b).symm.trans
      (congrArg (fundamentalGroupHom A.hom xi) hb)
  rw [extendFiberOverAut_pointedDeck, he]

/-- An ambient element centralizing the covering subgroup induces the identity
on the actual pointed fundamental group under its geometric deck comparison. -/
theorem deckPointed_eq_self_of_centralizes
    (hc : ∀ a : π₁ᵉᵗ(xi), Commute g (fundamentalGroupHom A.hom xi a))
    (a : π₁ᵉᵗ(xi)) :
    autHomOfCompIso (pullback σ.hom.left)
      (deckPointedGeometricFiberIso A xi σ g h) a = a := by
  apply (fundamentalGroupEquivStabilizerOfLift A xi).injective
  apply Subtype.ext
  rw [fundamentalGroupEquivStabilizerOfLift_coe,
    fundamentalGroupEquivStabilizerOfLift_coe, fundamentalGroupHom_deckPointed]
  rw [mul_assoc, ← (hc a).eq, inv_mul_cancel_left]

end AlgebraicGeometry.FiniteEtale
