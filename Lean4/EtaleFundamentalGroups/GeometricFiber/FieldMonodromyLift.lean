/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# Field automorphisms on the actual lifted geometric point

The homomorphism induced by an actual field-valued scheme morphism sends the
field Galois action to precomposition of the actual geometric lift by Spec σ.
This includes generic points and does not require a connected cover.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] IsSepClosure.sep_closed

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
  {X : Scheme.{u}} (f : Spec (.of k) ⟶ X)

/-- The actual induced fundamental-group action is the original field
Galois automorphism acting on the geometric lift by precomposition. -/
theorem fundamentalGroupHom_field_fiberLift
    (W : FiniteEtale X) (σ : Ω ≃ₐ[k] Ω)
    (x : (fiber ((ξ k Ω) ≫ f)).obj W) :
    (fiberObjEquivHom ((ξ k Ω) ≫ f) W
      ((fundamentalGroupHom f (ξ k Ω) (toAut (fib k Ω) (Ω ≃ₐ[k] Ω) σ)).hom.app W x)).left =
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
          (fiberObjEquivHom ((ξ k Ω) ≫ f) W x).left := by
  let t := pullbackFiberIso f (ξ k Ω)
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso (t.hom.app W)).surjective x
  let a := toAut (fib k Ω) (Ω ≃ₐ[k] Ω) σ
  have hact := pullbackFiberIso_hom_fundamentalGroupHom_apply f (ξ k Ω) a W y
  have hfield :
      (fiberObjEquivHom (ξ k Ω) ((pullback f).obj W)
        (a.hom.app ((pullback f).obj W) y)).left =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
        (fiberObjEquivHom (ξ k Ω) ((pullback f).obj W) y).left := by
    change (fiberObjEquivHom (ξ k Ω) ((pullback f).obj W)
      ((toAut (fib k Ω) (Ω ≃ₐ[k] Ω) σ).hom.app _ y)).left = _
    rw [toAut_hom_app_apply, algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
    exact algEquiv_smul_hom k Ω _ σ _
  calc
    (fiberObjEquivHom ((ξ k Ω) ≫ f) W
        ((fundamentalGroupHom f (ξ k Ω) a).hom.app W (t.hom.app W y))).left =
        (fiberObjEquivHom ((ξ k Ω) ≫ f) W
          (t.hom.app W (a.hom.app ((pullback f).obj W) y))).left :=
      congrArg (fun z => (fiberObjEquivHom ((ξ k Ω) ≫ f) W z).left) hact.symm
    _ = (fiberObjEquivHom (ξ k Ω) ((pullback f).obj W)
          (a.hom.app ((pullback f).obj W) y)).left ≫ Limits.pullback.fst W.hom f :=
      pullbackFiberIso_hom_fiberObjEquivHom_left f (ξ k Ω) W _
    _ = (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
          (fiberObjEquivHom (ξ k Ω) ((pullback f).obj W) y).left) ≫
            Limits.pullback.fst W.hom f := congrArg (· ≫ Limits.pullback.fst W.hom f) hfield
    _ = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫
          (fiberObjEquivHom ((ξ k Ω) ≫ f) W (t.hom.app W y)).left :=
      (Category.assoc _ _ _).trans (congrArg
        (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ ·)
          (pullbackFiberIso_hom_fiberObjEquivHom_left f (ξ k Ω) W y).symm)

end AlgebraicGeometry.FiniteEtale
