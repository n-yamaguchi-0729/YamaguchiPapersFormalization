/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Functoriality over a tower of fields

For a tower of fields `k → K → Ω`, base change from `k` to `K` is
compatible with the two geometric fiber functors valued in `Ω`.  The
comparison below is written directly on geometric points; this makes its
compatibility with scalar restriction on absolute Galois groups explicit.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable (k K Ω : Type u)
variable [Field k] [Field K] [Field Ω]
variable [Algebra k K] [Algebra K Ω] [Algebra k Ω]
variable [IsScalarTower k K Ω]

/-- The geometric point of `Spec k` obtained through `Spec K` is the
geometric point defined by the composite algebra structure. -/
lemma fieldGeometricPoint_comp :
    ξ K Ω ≫ ξ k K = ξ k Ω := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply k K Ω x).symm

/-- On geometric points, the fiber of a base changed finite étale cover is
the original geometric fiber. -/
noncomputable def fieldPullbackOverEquiv
    (X : FiniteEtale (Spec (.of k))) :
    (Over.mk (ξ K Ω) ⟶ ((pullback (ξ k K)).obj X).toComma) ≃
      (Over.mk (ξ k Ω) ⟶ X.toComma) where
  toFun z :=
    Over.homMk (z.left ≫ Limits.pullback.fst X.hom (ξ k K)) (by
      change (z.left ≫ Limits.pullback.fst X.hom (ξ k K)) ≫ X.hom = ξ k Ω
      rw [← fieldGeometricPoint_comp k K Ω]
      have hz : z.left ≫ Limits.pullback.snd X.hom (ξ k K) = ξ K Ω := by
        exact z.w
      have hcondition :
          Limits.pullback.fst X.hom (ξ k K) ≫ X.hom =
            Limits.pullback.snd X.hom (ξ k K) ≫ ξ k K :=
        Limits.pullback.condition
      erw [Category.assoc, hcondition, ← Category.assoc, hz])
  invFun x :=
    Over.homMk
      (Limits.pullback.lift x.left (ξ K Ω)
        (x.w.trans (fieldGeometricPoint_comp k K Ω).symm))
      (Limits.pullback.lift_snd _ _ _)
  left_inv z := by
    apply CategoryTheory.Over.OverMorphism.ext
    apply Limits.pullback.hom_ext
    · exact Limits.pullback.lift_fst _ _ _
    · have hz : z.left ≫ Limits.pullback.snd X.hom (ξ k K) = ξ K Ω := by
        exact z.w
      exact (Limits.pullback.lift_snd _ _ _).trans hz.symm
  right_inv x := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact Limits.pullback.lift_fst _ _ _

private lemma fieldPullbackOverEquiv_naturality
    {X Y : FiniteEtale (Spec (.of k))} (f : X ⟶ Y)
    (z : Over.mk (ξ K Ω) ⟶ ((pullback (ξ k K)).obj X).toComma) :
    fieldPullbackOverEquiv k K Ω Y
        (z ≫ ((pullback (ξ k K)).map f).hom) =
      fieldPullbackOverEquiv k K Ω X z ≫ f.hom := by
  apply CategoryTheory.Over.OverMorphism.ext
  have hmap :
      ((pullback (ξ k K)).map f).left ≫
          Limits.pullback.fst Y.hom (ξ k K) =
        Limits.pullback.fst X.hom (ξ k K) ≫ f.left := by
    change Limits.pullback.lift
        (Limits.pullback.fst X.hom (ξ k K) ≫ f.left)
        (Limits.pullback.snd X.hom (ξ k K)) _ ≫
          Limits.pullback.fst Y.hom (ξ k K) =
      Limits.pullback.fst X.hom (ξ k K) ≫ f.left
    exact Limits.pullback.lift_fst _ _ _
  change (z.left ≫ ((pullback (ξ k K)).map f).left) ≫
      Limits.pullback.fst Y.hom (ξ k K) =
    (z.left ≫ Limits.pullback.fst X.hom (ξ k K)) ≫ f.left
  erw [Category.assoc, hmap, ← Category.assoc]

section

variable [IsSepClosed Ω]

/-- The pointwise comparison between the geometric fiber after base change
and the original geometric fiber. -/
noncomputable def fieldFiberEquiv
    (X : FiniteEtale (Spec (.of k))) :
    ((pullback (ξ k K) ⋙ fib K Ω).obj X) ≃ (fib k Ω).obj X :=
  (fiberObjEquivHom (ξ K Ω) ((pullback (ξ k K)).obj X)).trans
    ((fieldPullbackOverEquiv k K Ω X).trans
      (fiberObjEquivHom (ξ k Ω) X).symm)

@[simp]
lemma fiberObjEquivHom_fieldFiberEquiv
    (X : FiniteEtale (Spec (.of k)))
    (x : (pullback (ξ k K) ⋙ fib K Ω).obj X) :
    fiberObjEquivHom (ξ k Ω) X (fieldFiberEquiv k K Ω X x) =
      fieldPullbackOverEquiv k K Ω X
        (fiberObjEquivHom (ξ K Ω) ((pullback (ξ k K)).obj X) x) := by
  change fiberObjEquivHom (ξ k Ω) X
      ((fiberObjEquivHom (ξ k Ω) X).symm
        (fieldPullbackOverEquiv k K Ω X
          (fiberObjEquivHom (ξ K Ω) ((pullback (ξ k K)).obj X) x))) = _
  exact Equiv.apply_symm_apply _ _

/-- Pullback from `Spec k` to `Spec K`, followed by the geometric fiber in
`Ω`, is naturally isomorphic to the geometric fiber over `Spec k`. -/
noncomputable def fieldPullbackFiberIso :
    pullback (ξ k K) ⋙ fib K Ω ≅ fib k Ω :=
  NatIso.ofComponents
    (fun X ↦ FintypeCat.equivEquivIso (fieldFiberEquiv k K Ω X))
    (fun {X Y} f ↦ by
      ext x
      change fieldFiberEquiv k K Ω Y
          ((fib K Ω).map ((pullback (ξ k K)).map f) x) =
        (fib k Ω).map f (fieldFiberEquiv k K Ω X x)
      apply (fiberObjEquivHom (ξ k Ω) Y).injective
      rw [fiberObjEquivHom_fieldFiberEquiv,
        ← fiberObjEquivHom_naturality]
      rw [← fiberObjEquivHom_naturality,
        fiberObjEquivHom_fieldFiberEquiv]
      exact fieldPullbackOverEquiv_naturality k K Ω f
        (fiberObjEquivHom (ξ K Ω) ((pullback (ξ k K)).obj X) x))

omit [IsSepClosed Ω] in
lemma fieldPullbackOverEquiv_smul
    (X : FiniteEtale (Spec (.of k))) (σ : Ω ≃ₐ[K] Ω)
    (z : Over.mk (ξ K Ω) ⟶ ((pullback (ξ k K)).obj X).toComma) :
    fieldPullbackOverEquiv k K Ω X (σ • z) =
      σ.restrictScalars k • fieldPullbackOverEquiv k K Ω X z := by
  apply CategoryTheory.Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ z.left) ≫
      Limits.pullback.fst X.hom (ξ k K) =
    Spec.map (CommRingCat.ofHom (σ.restrictScalars k : Ω →+* Ω)) ≫
      (z.left ≫ Limits.pullback.fst X.hom (ξ k K))
  exact Category.assoc _ _ _

/-- The comparison of geometric fibers intertwines the absolute Galois
action over `K` with scalar restriction to `k`. -/
theorem fieldFiberEquiv_smul
    (X : FiniteEtale (Spec (.of k))) (σ : Ω ≃ₐ[K] Ω)
    (x : (fib K Ω).obj ((pullback (ξ k K)).obj X)) :
    fieldFiberEquiv k K Ω X (σ • x) =
      σ.restrictScalars k • fieldFiberEquiv k K Ω X x := by
  apply (fiberObjEquivHom (ξ k Ω) X).injective
  rw [fiberObjEquivHom_fieldFiberEquiv,
    algEquiv_smul_fiber_def, Equiv.apply_symm_apply]
  rw [algEquiv_smul_fiber_def, Equiv.apply_symm_apply,
    fiberObjEquivHom_fieldFiberEquiv]
  exact fieldPullbackOverEquiv_smul k K Ω X σ
    (fiberObjEquivHom (ξ K Ω) ((pullback (ξ k K)).obj X) x)

end

/-- The absolute Galois group identified with the automorphism group of its
geometric fiber functor, using an explicitly supplied separably-closed
structure on the common overfield. -/
noncomputable def absoluteGaloisToFiberAutMulEquiv
    (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω]
    [IsSepClosure F Ω] (hΩ : IsSepClosed Ω) :
    (Ω ≃ₐ[F] Ω) ≃* Aut (fib F Ω) := by
  letI : IsSepClosed Ω := hΩ
  exact CategoryTheory.PreGaloisCategory.toAutMulEquiv
    (fib F Ω) (Ω ≃ₐ[F] Ω)

/-- The homomorphism of geometric-fiber automorphism groups induced by
pullback from `Spec k` to `Spec K`, with the comparison on points fixed by
`fieldPullbackFiberIso`. -/
noncomputable def fieldFundamentalGroupHom
    (hΩ : IsSepClosed Ω) :
    Aut (fib K Ω) →ₜ* Aut (fib k Ω) := by
  letI : IsSepClosed Ω := hΩ
  exact CategoryTheory.PreGaloisCategory.autHomOfCompIso
    (pullback (ξ k K)) (fieldPullbackFiberIso k K Ω)

section

variable [IsSepClosure k Ω] [IsSepClosure K Ω]

private theorem fieldFundamentalGroupHom_toAutMulEquiv_core
    [IsSepClosed Ω] (σ : Ω ≃ₐ[K] Ω) :
    CategoryTheory.PreGaloisCategory.autHomOfCompIso
        (pullback (ξ k K)) (fieldPullbackFiberIso k K Ω)
        (CategoryTheory.PreGaloisCategory.toAutMulEquiv
          (fib K Ω) (Ω ≃ₐ[K] Ω) σ) =
      CategoryTheory.PreGaloisCategory.toAutMulEquiv
        (fib k Ω) (Ω ≃ₐ[k] Ω) (σ.restrictScalars k) := by
  apply Aut.ext
  ext X x
  rw [CategoryTheory.PreGaloisCategory.autHomOfCompIso_apply]
  change fieldFiberEquiv k K Ω X
      (σ • (show (fib K Ω).obj ((pullback (ξ k K)).obj X) from
        (fieldPullbackFiberIso k K Ω).inv.app X x)) =
    σ.restrictScalars k • x
  rw [fieldFiberEquiv_smul]
  change σ.restrictScalars k •
      ((fieldPullbackFiberIso k K Ω).hom.app X
        ((fieldPullbackFiberIso k K Ω).inv.app X x)) = _
  exact congrArg (fun y ↦ σ.restrictScalars k • y)
    (FintypeCat.inv_hom_id_apply ((fieldPullbackFiberIso k K Ω).app X) x)

/-- Under the canonical identifications of the two geometric-fiber
fundamental groups with absolute Galois groups, the homomorphism induced by
`Spec K ⟶ Spec k` is restriction of scalars. -/
theorem fieldFundamentalGroupHom_toAutMulEquiv
    (σ : Ω ≃ₐ[K] Ω) :
    fieldFundamentalGroupHom k K Ω (IsSepClosure.sep_closed k)
        (absoluteGaloisToFiberAutMulEquiv K Ω
          (IsSepClosure.sep_closed k) σ) =
      absoluteGaloisToFiberAutMulEquiv k Ω
        (IsSepClosure.sep_closed k) (σ.restrictScalars k) := by
  let : IsSepClosed Ω := IsSepClosure.sep_closed k
  exact fieldFundamentalGroupHom_toAutMulEquiv_core k K Ω σ

end

end AlgebraicGeometry.FiniteEtale

end
