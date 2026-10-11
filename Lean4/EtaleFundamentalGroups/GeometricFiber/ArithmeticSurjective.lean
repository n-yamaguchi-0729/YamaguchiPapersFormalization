/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.GaloisCategories.Surjectivity
import EtaleFundamentalGroups.GaloisCategories.FiberIso
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.GeometricFiber.OpenImmersionSurjective
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import EtaleFundamentalGroups.GeometricFiber.BasePoint
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Arithmetic Surjective

A geometrically connected scheme over a field induces a surjection on
the fundamental group of that field.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- A geometrically connected scheme over a field induces a surjection on
the fundamental group of that field. -/
theorem fundamentalGroupHom_surjective_of_geometricallyConnected
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) :
    Function.Surjective (fundamentalGroupHom f xi) := by
  let : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton f
  let : PreservesLimitsOfShape (Discrete PEmpty.{1}) (pullback f) :=
    pullback_preservesLimitsOfShape_pempty f
  change Function.Surjective
    (autHomOfCompIso (pullback f) (pullbackFiberIso f xi))
  apply ((autHomOfCompIso_surjective_tfae
    (fiber (xi ≫ f)) (fiber xi) (pullback f)
    (pullbackFiberIso f xi)).out 3 1).mp
  intro W hW
  let : IsConnected W := hW
  let : ConnectedSpace W.left := connectedSpace_left_of_isConnected W
  let : Field Γ(W.left, ⊤) := (isField_of_isConnected k W).toField
  let : Subsingleton W.left := ⟨fun x y ↦ by
    apply W.left.isoSpec.hom.homeomorph.injective
    have : Subsingleton (Spec Γ(W.left, ⊤)) := by
      change Subsingleton (PrimeSpectrum Γ(W.left, ⊤))
      infer_instance
    exact Subsingleton.elim _ _⟩
  let : GeometricallyConnected (Limits.pullback.fst W.hom f) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_hasPullback W.hom f).flip ‹GeometricallyConnected f›
  let : ConnectedSpace ((pullback f).obj W).left := by
    change ConnectedSpace ↑(Limits.pullback W.hom f)
    exact GeometricallyConnected.connectedSpace_of_subsingleton
      (S := W.left) (Limits.pullback.fst W.hom f)
  exact isConnected_of_connectedSpace_left ((pullback f).obj W)

/-- The arithmetic map to the absolute Galois group of `k`, with the
comparison of geometric points supplied by the fiber-functor comparison theorem. -/
def arithmeticFundamentalGroupHom
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) : π₁ᵉᵗ(xi) →ₜ* (K ≃ₐ[k] K) := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let e : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k K) :=
    { toHomeomorph := toAutHomeo (fib k K) (K ≃ₐ[k] K)
      map_mul' := (toAut (fib k K) (K ≃ₐ[k] K)).map_mul }
  let t : fiber (xi ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k K)).some
  exact (ContinuousMonoidHom.toContinuousMonoidHom e.symm).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (continuousConjAut t)).comp
      (fundamentalGroupHom f xi))

/-- The arithmetic fundamental-group map of a geometrically connected
scheme over `k` is surjective. -/
theorem arithmeticFundamentalGroupHom_surjective
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [GeometricallyConnected f]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ X) :
    Function.Surjective (arithmeticFundamentalGroupHom k K f xi) := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let e : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k K) :=
    { toHomeomorph := toAutHomeo (fib k K) (K ≃ₐ[k] K)
      map_mul' := (toAut (fib k K) (K ≃ₐ[k] K)).map_mul }
  let t : fiber (xi ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k K)).some
  change Function.Surjective
    (fun a ↦ e.symm ((continuousConjAut t) (fundamentalGroupHom f xi a)))
  exact e.symm.surjective.comp ((continuousConjAut t).surjective.comp
    (fundamentalGroupHom_surjective_of_geometricallyConnected f xi))

end AlgebraicGeometry.FiniteEtale
