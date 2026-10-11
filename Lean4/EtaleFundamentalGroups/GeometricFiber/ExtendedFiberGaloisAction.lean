/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.AlgebraicClosure
import EtaleFundamentalGroups.GeometricFiber.PullbackFiberPoint

/-!
# The literal point action of the extended residue Galois comparison

The canonical extension of the separable-closure fiber carries a compatible
automorphism to its actual spectrum action on the larger geometric point.
The original fundamental-group morphism preserves this same point action.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k C Ω : Type u) [Field k] [Field C] [Field Ω]
  [Algebra k C] [IsSepClosure k C] [Algebra C Ω] [Algebra k Ω]
  [IsScalarTower k C Ω] [IsSepClosed Ω]

/-- The extended-fiber Galois comparison uses the given compatible field map
on every actual geometric point. -/
theorem absoluteGaloisToExtendedFiberAut_point
    (σ : Gal(C/k)) (ρ : Ω →+* Ω)
    (hρ : ρ.comp (algebraMap C Ω) = (algebraMap C Ω).comp σ.toRingHom)
    (X : FiniteEtale (Spec (.of k))) (x : (fib k Ω).obj X) :
    (fiberObjEquivHom (ξ k Ω) X
      ((absoluteGaloisToExtendedFiberAut k C Ω σ).hom.app X x)).left =
      Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom (ξ k Ω) X x).left := by
  have : IsSepClosed C := IsSepClosure.sep_closed k
  let t := fieldFiberExtensionIso k C Ω
  let y := t.inv.app X x
  have hy : t.hom.app X y = x := FintypeCat.inv_hom_id_apply (t.app X) x
  have hspec : ξ C Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) =
      Spec.map (CommRingCat.ofHom ρ) ≫ ξ C Ω := by
    exact (Spec.map_comp (CommRingCat.ofHom σ.toRingHom)
      (CommRingCat.ofHom (algebraMap C Ω))).symm.trans
      ((congrArg (fun r : C →+* Ω => Spec.map (CommRingCat.ofHom r)) hρ.symm).trans
        (Spec.map_comp (CommRingCat.ofHom (algebraMap C Ω)) (CommRingCat.ofHom ρ)))
  change (fiberObjEquivHom (ξ k Ω) X (t.hom.app X (σ • y))).left = _
  calc
    _ = ξ C Ω ≫ (fiberObjEquivHom (ξ k C) X (σ • y)).left :=
      fieldFiberExtensionIso_point k C Ω X (σ • y)
    _ = ξ C Ω ≫ (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        (fiberObjEquivHom (ξ k C) X y).left) := by
      rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply, algEquiv_smul_hom]
      rfl
    _ = (ξ C Ω ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) ≫
        (fiberObjEquivHom (ξ k C) X y).left := (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom ρ) ≫ ξ C Ω) ≫
        (fiberObjEquivHom (ξ k C) X y).left :=
      congrArg (fun z : Spec (.of Ω) ⟶ Spec (.of C) =>
        z ≫ (fiberObjEquivHom (ξ k C) X y).left) hspec
    _ = Spec.map (CommRingCat.ofHom ρ) ≫
        (ξ C Ω ≫ (fiberObjEquivHom (ξ k C) X y).left) := Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom ρ) ≫
        (fiberObjEquivHom (ξ k Ω) X (t.hom.app X y)).left :=
      congrArg (fun z : Spec (.of Ω) ⟶ X.left => Spec.map (CommRingCat.ofHom ρ) ≫ z)
        (fieldFiberExtensionIso_point k C Ω X y).symm
    _ = _ := congrArg (fun z => Spec.map (CommRingCat.ofHom ρ) ≫
      (fiberObjEquivHom (ξ k Ω) X z).left) hy

variable {Ω}

omit [Algebra k C] [IsSepClosure k C] [Algebra C Ω] [Algebra k Ω] [IsScalarTower k C Ω] in
/-- The actual scheme-induced homomorphism preserves a prescribed point action. -/
theorem fundamentalGroupHom_point_of_point_action
    {S T : Scheme.{u}} (f : S ⟶ T) (s : Spec (.of Ω) ⟶ S)
    (a : π₁ᵉᵗ(s)) (ρ : Ω →+* Ω)
    (ha : ∀ (X : FiniteEtale S) (x : (fiber s).obj X),
      (fiberObjEquivHom s X (a.hom.app X x)).left =
        Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom s X x).left)
    (Y : FiniteEtale T) (y : (fiber (s ≫ f)).obj Y) :
    (fiberObjEquivHom (s ≫ f) Y ((fundamentalGroupHom f s a).hom.app Y y)).left =
      Spec.map (CommRingCat.ofHom ρ) ≫ (fiberObjEquivHom (s ≫ f) Y y).left := by
  obtain ⟨x, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective
    ((pullbackFiberIso f s).hom.app Y)).mp inferInstance).surjective y
  rw [← pullbackFiberIso_hom_fundamentalGroupHom_apply,
    pullbackFiberIso_hom_fiberObjEquivHom_left, ha,
    pullbackFiberIso_hom_fiberObjEquivHom_left]
  exact Category.assoc _ _ _

end AlgebraicGeometry.FiniteEtale
