/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.HeightOne.FiniteFreeHom

/-!
# Reconstructing algebra morphisms after linear descent

Codimension-one intersection arguments naturally descend a generic-fibre
linear map before they establish its multiplicative structure.  If the
descended map becomes an algebra morphism after composition with an
injective algebra map, preservation of one and multiplication reflects back
to the original target.  This file packages that reconstruction step.
-/

namespace EtaleFundamentalGroups

universe u v w z

noncomputable section

/-- A linear map which becomes an algebra morphism after composition with an
injective algebra map underlies a unique algebra morphism. -/
theorem existsUnique_algHom_of_comp_eq_of_injective
    {R : Type u} {S : Type v} {T : Type w} {U : Type z}
    [CommSemiring R] [Semiring S] [Semiring T] [Semiring U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    (g : S →ₗ[R] T) (ι : T →ₐ[R] U) (hι : Function.Injective ι)
    (f : S →ₐ[R] U) (hcomp : ι.toLinearMap.comp g = f.toLinearMap) :
    ∃! φ : S →ₐ[R] T, φ.toLinearMap = g := by
  have hone : g 1 = 1 := by
    apply hι
    have h := LinearMap.congr_fun hcomp 1
    simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_one] using h
  have hmul (x y : S) : g (x * y) = g x * g y := by
    apply hι
    have hxy : ι (g (x * y)) = f (x * y) := by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
        LinearMap.congr_fun hcomp (x * y)
    have hx : ι (g x) = f x := by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
        LinearMap.congr_fun hcomp x
    have hy : ι (g y) = f y := by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
        LinearMap.congr_fun hcomp y
    calc
      ι (g (x * y)) = f (x * y) := hxy
      _ = f x * f y := map_mul f x y
      _ = ι (g x) * ι (g y) := congrArg₂ (fun a b : U ↦ a * b) hx.symm hy.symm
      _ = ι (g x * g y) := (map_mul ι (g x) (g y)).symm
  let φ : S →ₐ[R] T := AlgHom.ofLinearMap g hone hmul
  refine ⟨φ, AlgHom.toLinearMap_ofLinearMap g hone hmul, ?_⟩
  intro ψ hψ
  apply AlgHom.toLinearMap_injective
  exact hψ.trans (AlgHom.toLinearMap_ofLinearMap g hone hmul).symm

/-- A linear equivalence which becomes an algebra morphism after composition
with an injective algebra map underlies a unique algebra equivalence. -/
theorem existsUnique_algEquiv_of_comp_eq_of_injective
    {R : Type u} {S : Type v} {T : Type w} {U : Type z}
    [CommSemiring R] [Semiring S] [Semiring T] [Semiring U]
    [Algebra R S] [Algebra R T] [Algebra R U]
    (e : S ≃ₗ[R] T) (ι : T →ₐ[R] U) (hι : Function.Injective ι)
    (f : S →ₐ[R] U)
    (hcomp : ι.toLinearMap.comp e.toLinearMap = f.toLinearMap) :
    ∃! φ : S ≃ₐ[R] T, φ.toLinearEquiv = e := by
  obtain ⟨φ, hφ, -⟩ :=
    existsUnique_algHom_of_comp_eq_of_injective
      e.toLinearMap ι hι f hcomp
  have hφbijective : Function.Bijective φ := by
    change Function.Bijective φ.toLinearMap
    rw [hφ]
    exact e.bijective
  let E : S ≃ₐ[R] T := AlgEquiv.ofBijective φ hφbijective
  have hE : E.toLinearEquiv = e := by
    apply LinearEquiv.toLinearMap_injective
    change E.toLinearMap = e.toLinearMap
    calc
      E.toLinearMap = φ.toLinearMap := by
        exact AlgEquiv.toLinearMap_ofBijective φ hφbijective
      _ = e.toLinearMap := hφ
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  exact AlgEquiv.toLinearEquiv_injective (hE'.trans hE.symm)

end

end EtaleFundamentalGroups
