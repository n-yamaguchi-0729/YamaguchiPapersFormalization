/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import EtaleFundamentalGroups.GeometricFiber.ArithmeticConnected
import EtaleFundamentalGroups.GeometricFiber.ArithmeticComposite

/-!
# Arithmetic Map

Identifying the field fundamental group with its absolute Galois group
preserves the kernel of the arithmetic map.
-/

noncomputable section
universe u
open CategoryTheory Limits CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.FiniteEtale

/-- Identifying the field fundamental group with its absolute Galois group
preserves the kernel of the arithmetic map. -/
theorem arithmeticFundamentalGroupHom_ker
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsSepClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
    (arithmeticFundamentalGroupHom k K f xi).toMonoidHom.ker =
      (fundamentalGroupHom f xi).toMonoidHom.ker := by
  let : IsSepClosed K := IsSepClosure.sep_closed k
  let e : (K ≃ₐ[k] K) ≃ₜ* Aut (fib k K) :=
    { toHomeomorph := toAutHomeo (fib k K) (K ≃ₐ[k] K)
      map_mul' := (toAut (fib k K) (K ≃ₐ[k] K)).map_mul }
  let t : fiber (xi ≫ f) ≅ fib k K :=
    (nonempty_fiber_iso (xi ≫ f) (ξ k K)).some
  ext a
  change e.symm ((continuousConjAut t) (fundamentalGroupHom f xi a)) = 1 ↔
    fundamentalGroupHom f xi a = 1
  rw [← map_one e.symm, e.symm.injective.eq_iff,
    ← map_one (continuousConjAut t), (continuousConjAut t).injective.eq_iff]

/-- The arithmetic map to an absolute Galois group is surjective when a
separably closed constant extension is connected. -/
theorem arithmeticFundamentalGroupHom_surjective_of_connected_constantField
    (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [IsSepClosure k K] [Algebra k L] [IsSepClosed L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace ↑(Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L))) f)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (xi : Spec (.of Ω) ⟶ X) :
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
    (fundamentalGroupHom_surjective_of_connected_constantField k L f xi))

end AlgebraicGeometry.FiniteEtale
