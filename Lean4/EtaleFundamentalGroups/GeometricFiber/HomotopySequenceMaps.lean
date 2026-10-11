/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.GaloisCategories.Surjectivity
import EtaleFundamentalGroups.GeometricFiber.ArithmeticComposite
import EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The maps in the homotopy sequence

For the actual geometric-fiber pullback, the two original fundamental-group
maps have trivial composite.  The proof factors their composite through the
fundamental group of the separably closed field, preserving the canonical
fiber comparisons and the equalities of geometric points.

For a flat morphism locally of finite presentation with geometrically
connected fibers, the map to the fundamental group of a connected base is
surjective.  This follows from connectedness of actual pullbacks of connected
finite étale covers.  These are the composite and surjectivity inputs to
Stacks Project, Proposition 58.15.2 (tag 0C0J); middle exactness is separate.
-/

noncomputable section

open CategoryTheory Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- The two original maps from a geometric fiber to its total space and base
have trivial composite. -/
theorem fundamentalGroupHom_geometricFiber_comp_eq_one
    {X S : Scheme.{u}} (f : X ⟶ S)
    {L : Type u} [Field L] [IsSepClosed L] (s : Spec (.of L) ⟶ S)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback s f) :
    (fundamentalGroupHom f (xi ≫ Limits.pullback.snd s f)).comp
      (fundamentalGroupHom (Limits.pullback.snd s f) xi) = 1 := by
  let p : Limits.pullback s f ⟶ X := Limits.pullback.snd s f
  let q : Limits.pullback s f ⟶ Spec (.of L) := Limits.pullback.fst s f
  let m : Limits.pullback s f ⟶ S := p ≫ f
  have hm : m = q ≫ s := Limits.pullback.condition.symm
  have hp : (xi ≫ p) ≫ f = xi ≫ m := Category.assoc xi p f
  have hq : (xi ≫ q) ≫ s = xi ≫ m := by
    rw [Category.assoc, ← hm]
  have hs : Subsingleton π₁ᵉᵗ(xi ≫ q) :=
    subsingleton_fundamentalGroup_of_isSepClosed L (xi ≫ q)
  have transport_eq_one (eta₁ eta₂ : Spec (.of Ω) ⟶ S)
      (h : eta₁ = eta₂) (b : π₁ᵉᵗ(eta₁)) :
      (h ▸ b) = (1 : π₁ᵉᵗ(eta₂)) ↔ b = 1 := by
    subst eta₂
    rfl
  apply ContinuousMonoidHom.ext
  intro a
  change fundamentalGroupHom f (xi ≫ p) (fundamentalGroupHom p xi a) = 1
  have hpcomp := fundamentalGroupHom_comp_of_eq p f m rfl xi hp a
  have hqcomp := fundamentalGroupHom_comp_of_eq q s m hm xi hq a
  have hqzero : fundamentalGroupHom q xi a = 1 := hs.elim _ _
  have hmzero : fundamentalGroupHom m xi a = 1 := by
    rw [← hqcomp]
    apply (transport_eq_one ((xi ≫ q) ≫ s) (xi ≫ m) hq
      (fundamentalGroupHom s (xi ≫ q) (fundamentalGroupHom q xi a))).mpr
    rw [hqzero, map_one]
  exact (transport_eq_one ((xi ≫ p) ≫ f) (xi ≫ m) hp
    (fundamentalGroupHom f (xi ≫ p) (fundamentalGroupHom p xi a))).mp
      (hpcomp.trans hmzero)

/-- Flat morphisms locally of finite presentation with geometrically
connected fibers induce surjections on fundamental groups of connected bases. -/
theorem fundamentalGroupHom_surjective_of_flat_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]
    [ConnectedSpace S]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) :
    Function.Surjective (fundamentalGroupHom f xi) := by
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace f f.isOpenMap
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  change Function.Surjective (autHomOfCompIso (pullback f) (pullbackFiberIso f xi))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (xi ≫ f)) (fiber xi) (pullback f) (pullbackFiberIso f xi)).out 3 1).mp
  intro W hW
  let : IsConnected W := hW
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let q : Limits.pullback W.hom f ⟶ W.left := Limits.pullback.fst W.hom f
  let : GeometricallyConnected q :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback W.hom f).flip ‹GeometricallyConnected f›
  let : UniversallyOpen q :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen)
      (IsPullback.of_hasPullback W.hom f).flip (inferInstance : UniversallyOpen f)
  let : ConnectedSpace ((pullback f).obj W).left := by
    change ConnectedSpace ↑(Limits.pullback W.hom f)
    exact GeometricallyConnected.connectedSpace (S := W.left) q q.isOpenMap
  exact isConnected_of_connectedSpace_left ((pullback f).obj W)

end AlgebraicGeometry.FiniteEtale
