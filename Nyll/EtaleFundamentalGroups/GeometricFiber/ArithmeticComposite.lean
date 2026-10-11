/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticSurjective
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition

/-!
# Arithmetic Composite

The fundamental group of a separably closed field at any geometric point is trivial.
-/

noncomputable section
universe u
open CategoryTheory Limits CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.FiniteEtale

/-- The fundamental group of a separably closed field at any geometric point is trivial. -/
theorem subsingleton_fundamentalGroup_of_isSepClosed
    (L : Type u) [Field L] [IsSepClosed L]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (eta : Spec (.of Ω) ⟶ Spec (.of L)) :
    Subsingleton π₁ᵉᵗ(eta) := by
  let t : fiber eta ≅ fib L L := (nonempty_fiber_iso eta (ξ L L)).some
  let e : (L ≃ₐ[L] L) ≃* Aut (fib L L) := toAutMulEquiv (fib L L) (L ≃ₐ[L] L)
  have hs : Subsingleton (Aut (fib L L)) := e.symm.injective.subsingleton
  exact (continuousConjAut t).injective.subsingleton

/-- The geometric and arithmetic maps for a separably closed constant field
have trivial composite. -/
theorem fundamentalGroupHom_constantField_comp_eq_one
    (k L : Type u) [Field k] [Field L] [Algebra k L] [IsSepClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    (fundamentalGroupHom f (xi ≫ Limits.pullback.snd _ f)).comp
      (fundamentalGroupHom (Limits.pullback.snd _ f) xi) = 1 := by
  let φ : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let p := Limits.pullback.snd φ f
  let q := Limits.pullback.fst φ f
  let eta := (xi ≫ p) ≫ f
  have hpoint : (xi ≫ q) ≫ φ = eta := by
    dsimp [eta, p, q]
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
  have hs : Subsingleton π₁ᵉᵗ(xi ≫ q) :=
    subsingleton_fundamentalGroup_of_isSepClosed L (xi ≫ q)
  apply ContinuousMonoidHom.ext
  intro a
  change fundamentalGroupHom f (xi ≫ p) (fundamentalGroupHom p xi a) = 1
  have hc := fundamentalGroupHom_comp_conj_of_common_composite
    p f q φ (p ≫ f) rfl Limits.pullback.condition.symm xi eta rfl hpoint a
  have hz : fundamentalGroupHom q xi a = 1 := hs.elim _ _
  rw [hz, map_one] at hc
  have transportOne (η₁ η₂ : Spec (.of Ω) ⟶ Spec (.of k)) (h : η₁ = η₂) :
      h ▸ (1 : π₁ᵉᵗ(η₁)) = (1 : π₁ᵉᵗ(η₂)) := by
    subst η₂
    rfl
  simpa only [transportOne _ _ hpoint, map_one] using hc

/-- The same trivial composite after identifying the field fundamental group
with an absolute Galois group. -/
theorem arithmeticFundamentalGroupHom_constantField_comp_eq_one
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [IsSepClosure k K] [Algebra k L] [IsSepClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (xi : Spec (.of Ω) ⟶ Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f) :
    (arithmeticFundamentalGroupHom k K f (xi ≫ Limits.pullback.snd _ f)).comp
      (fundamentalGroupHom (Limits.pullback.snd _ f) xi) = 1 := by
  apply ContinuousMonoidHom.ext
  intro a
  have hc := DFunLike.congr_fun (fundamentalGroupHom_constantField_comp_eq_one k L f xi) a
  change fundamentalGroupHom f (xi ≫ Limits.pullback.snd _ f)
    (fundamentalGroupHom (Limits.pullback.snd _ f) xi a) = 1 at hc
  simp only [arithmeticFundamentalGroupHom, ContinuousMonoidHom.coe_comp, Function.comp_apply,
    hc, map_one, ContinuousMonoidHom.coe_one, Pi.one_apply]

end AlgebraicGeometry.FiniteEtale
