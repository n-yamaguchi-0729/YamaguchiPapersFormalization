/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
/-
Adapted pi1 source, including toolchain and proof repairs.
Reference revision (historical copy revision unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Point.lean

This module retains the upstream-derived algebra-homomorphism and field-point
morphism APIs. The NYLL completions of upstream unfinished geometric-fiber,
field, continuity, and Galois proofs remain in
Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup.
-/

module

public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry

/-!
# Field-valued points and automorphism actions

The upstream-derived actions on algebra homomorphisms and field-point morphisms,
the comparison with homomorphisms on global sections, and the detection of field
automorphisms by finite etale points.
-/

@[expose] public section

universe u

open CategoryTheory

section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

instance (L : Type*) [Semiring L] [Algebra k L] : MulAction (K ≃ₐ[k] K) (L →ₐ[k] K) where
  smul g x := (g : _ →ₐ[k] _).comp x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance (L : Type*) [Field L] [Algebra k L] [Algebra L K] [IsScalarTower k L K] [Normal k L]
    [Normal k K] :
    MulAction.IsPretransitive (K ≃ₐ[k] K) (L →ₐ[k] K) := by
  constructor
  intro x y
  obtain ⟨σx, (hx : σx.restrictNormal _ = _)⟩ :=
    AlgEquiv.restrictNormalHom_surjective K (x.restrictNormal' L)
  obtain ⟨σy, (hy : σy.restrictNormal _ = _)⟩ :=
    AlgEquiv.restrictNormalHom_surjective K (y.restrictNormal' L)
  use σx.symm.trans σy
  change ((σx.symm.trans σy : K ≃ₐ[k] K) : K →ₐ[k] K).comp x = y
  ext a
  have hy : y a = σy (algebraMap _ _ a) := by
    simp [← AlgEquiv.restrictNormal_commutes, hy, AlgHom.restrictNormal']
  have hx : x a = σx (algebraMap _ _ a) := by
    simp [← AlgEquiv.restrictNormal_commutes, hx, AlgHom.restrictNormal']
  simp [hx, hy]

end

namespace AlgebraicGeometry

namespace FiniteEtale

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ S)

unif_hint (X : FiniteEtale S) where
  ⊢ (forget S ⋙ coyoneda.obj ⟨Over.mk ξ⟩).obj X ≟ (Over.mk ξ ⟶ X.toComma)

variable (k K Ω : Type u) [Field k] [Field K] [Algebra k K] [Field Ω] [Algebra k Ω]
  [Algebra K Ω] [IsScalarTower k K Ω]

scoped notation3:arg "fib " k:arg K:arg =>
  FiniteEtale.fiber (Spec.map (CommRingCat.ofHom <| algebraMap k K))

scoped notation3:arg "ξ " k:arg K:arg => Spec.map (CommRingCat.ofHom <| algebraMap k K)

variable (X : FiniteEtale (Spec (.of k)))

noncomputable
instance : MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma) where
  smul g x := by
    let σ : (Over.mk (ξ k K)).left ⟶ (Over.mk (ξ k K)).left := by
      change Spec (.of K) ⟶ Spec (.of K)
      exact Spec.map (CommRingCat.ofHom (g : K →+* K))
    let σOver : Over.mk (ξ k K) ⟶ Over.mk (ξ k K) :=
      Over.homMk σ (by
        change Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ ξ k K = ξ k K
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← AlgEquiv.toAlgHom_toRingHom,
          AlgHom.comp_algebraMap])
    exact σOver ≫ x
  one_smul x := by
    ext1
    change Spec.map (CommRingCat.ofHom ((1 : K ≃ₐ[k] K) : K →+* K)) ≫ x.left = x.left
    simp [AlgEquiv.aut_one]
  mul_smul g h x := by
    ext1
    change Spec.map (CommRingCat.ofHom ((g * h : K ≃ₐ[k] K) : K →+* K)) ≫ x.left =
      Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (h : K →+* K)) ≫ x.left
    simp [AlgEquiv.aut_mul, Category.assoc]

@[simp]
lemma algEquiv_smul_hom (g : K ≃ₐ[k] K) (x : Over.mk (ξ k K) ⟶ X.toComma) :
    (g • x).left = Spec.map (CommRingCat.ofHom (g : K →+* K)) ≫ x.left :=
  rfl

scoped instance : TopologicalSpace (Over.mk (ξ k K) ⟶ X.toComma) := ⊥

noncomputable
instance : MulAction (K ≃ₐ[k] K) ((forget _ ⋙ coyoneda.obj ⟨Over.mk (ξ k K)⟩).obj X) :=
  fast_instance% inferInstanceAs <| MulAction (K ≃ₐ[k] K) (Over.mk (ξ k K) ⟶ X.toComma)


/-- Identify morphisms from the field point to a finite etale scheme with algebra homomorphisms
from its global sections to the field. -/
noncomputable
def homEquivAlgHom (X : FiniteEtale (Spec (.of k))) :
    (Over.mk (ξ k K) ⟶ X.toComma) ≃ (Γ(X.left, ⊤) →ₐ[k] K) where
  toFun x :=
    { __ := RingHom.comp (Scheme.ΓSpecIso _).hom.hom x.left.appTop.hom,
      commutes' a := by
        have hbase :
            algebraMap k Γ(X.left, ⊤) =
              X.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom := by
          simp [RingHom.algebraMap_toAlgebra, Iso.commRingCatIsoToRingEquiv,
            RingEquiv.coe_ringHom_ofRingHom, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        have h :
            (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫ x.left.appTop ≫
                (Scheme.ΓSpecIso (.of K)).hom =
              CommRingCat.ofHom (algebraMap k K) := by
          have hx := Over.w x
          change x.left ≫ X.hom = ξ k K at hx
          calc
            (Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop ≫ x.left.appTop ≫
                (Scheme.ΓSpecIso (.of K)).hom =
              (Scheme.ΓSpecIso (.of k)).inv ≫
                (x.left ≫ X.hom).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
                  rw [Scheme.Hom.comp_appTop]
                  exact congrArg
                    (fun q ↦ (Scheme.ΓSpecIso (.of k)).inv ≫ q)
                    (Category.assoc X.hom.appTop x.left.appTop
                      (Scheme.ΓSpecIso (.of K)).hom).symm
            _ = (Scheme.ΓSpecIso (.of k)).inv ≫
                (ξ k K).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
                  rw [hx]
            _ = CommRingCat.ofHom (algebraMap k K) := by
                  rw [Scheme.ΓSpecIso_naturality]
                  simp
        rw [hbase]
        change (Scheme.ΓSpecIso (.of K)).hom.hom
          (x.left.appTop.hom
            (X.hom.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))) =
          (algebraMap k K) a
        have ha :=
          congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of K ↦ f.hom a) h
        rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply] at ha
        exact ha }
  invFun x := Over.homMk
      (Spec.map (CommRingCat.ofHom x.toRingHom :
        Γ(X.left, ⊤) ⟶ CommRingCat.of K) ≫ X.left.isoSpec.inv) <| by
    have := x.comp_algebraMap
    dsimp
    rw [← this]
    simp only [Category.assoc, CommRingCat.ofHom_comp, Spec.map_comp]
    congr
    rw [RingHom.algebraMap_toAlgebra]
    dsimp only [OverClass.fromOver_over, RingEquiv.toRingHom_eq_coe, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
    rw [Spec.map_comp, Scheme.Hom.appLE]
    simp only [TopologicalSpace.Opens.map_top]
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
    have hiso : (Scheme.ΓSpecIso (.of k)).inv =
        CommRingCat.ofHom (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toRingHom := by
      ext a
      rfl
    rw [hiso]
    simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  left_inv x := by
    ext1
    simp only [Over.homMk_left]
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
      Spec.map_comp, SpecMap_ΓSpecIso_hom]
    let f : Spec (.of K) ⟶ X.left := x.left
    change ((Spec (.of K)).toSpecΓ ≫ Spec.map f.appTop) ≫ X.left.isoSpec.inv = f
    rw [← Scheme.toSpecΓ_naturality f]
    simp
  right_inv x := by
    apply AlgHom.coe_ringHom_injective
    simp only [Over.homMk_left]
    change (Scheme.ΓSpecIso (.of K)).hom.hom.comp
        ((Spec.map (CommRingCat.ofHom x.toRingHom :
          Γ(X.left, ⊤) ⟶ CommRingCat.of K) ≫ X.left.isoSpec.inv).appTop.hom) =
      x.toRingHom
    rw [← CommRingCat.hom_comp, Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality, ← Category.assoc, ← Scheme.toSpecΓ_appTop X.left,
      ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv, Scheme.Hom.id_appTop,
      Category.id_comp]
    rfl

lemma homEquivAlgHom_smul (X : FiniteEtale (Spec (.of k))) (g : K ≃ₐ[k] K) (x) :
    (homEquivAlgHom k K X) (g • x) = g • (homEquivAlgHom k K X x) := by
  rw [homEquivAlgHom]
  dsimp only [Over.mk_left, AlgHom.toRingHom_eq_coe, Equiv.coe_fn_mk, algEquiv_smul_hom,
    Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, CommRingCat.hom_comp]
  change _ = (g : K →ₐ[k] K).comp _
  ext1 a
  dsimp only [AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply, AlgHom.coe_comp,
    AlgHom.coe_ofClass]
  change ((Spec.map (CommRingCat.ofHom (g : K →+* K))).appTop ≫
    (Scheme.ΓSpecIso (.of K)).hom).hom (x.left.appTop.hom a) = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

lemma eq_one_of_smul_eq [Algebra.IsSeparable k K] (g : K ≃ₐ[k] K)
    (H : ∀ (X : FiniteEtale (Spec (.of k))) (x : (Over.mk (ξ k K) ⟶ X.toComma)), g • x = x) :
    g = 1 := by
  ext x
  let L := IntermediateField.adjoin k {x}
  have : IsFiniteEtale (ξ k L) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    have : Algebra.IsIntegral k L := inferInstance
    let : Algebra.EssFiniteType k L := by
      rw [IntermediateField.essFiniteType_iff]
      exact IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x)
    let : Module.Finite k L :=
      Algebra.finite_of_essFiniteType_of_isAlgebraic
    have : Algebra.Etale k L :=
      ⟨.of_isSeparable k L, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    constructor
  let X : FiniteEtale (Spec (.of k)) := FiniteEtale.mk (ξ k L)
  let y : Over.mk (ξ k K) ⟶ X.toComma := by
    refine Over.homMk
      (Spec.map <| CommRingCat.ofHom (R := L) (S := K) L.subtype) ?_
    change Spec.map (CommRingCat.ofHom (R := L) (S := K) L.subtype) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k L)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_injective.eq_iff]
    ext a
    rfl
  specialize H X y
  replace H := congrArg
    (fun z : Over.mk (ξ k K) ⟶ X.toComma ↦ z.left) H
  simp only [Subalgebra.toSubsemiring_subtype,
    IntermediateField.coe_type_toSubalgebra, algEquiv_smul_hom, y, X] at H
  change
    Spec.map (CommRingCat.ofHom (R := K) (S := K) (g : K →+* K)) ≫
        Spec.map (CommRingCat.ofHom (R := L) (S := K) L.val) =
      Spec.map (CommRingCat.ofHom (R := L) (S := K) L.val) at H
  have Hring :
      CommRingCat.ofHom (R := L) (S := K) L.val ≫
          CommRingCat.ofHom (R := K) (S := K) (g : K →+* K) =
        CommRingCat.ofHom (R := L) (S := K) L.val := by
    apply Spec.map_injective
    simpa only [Spec.map_comp] using H
  have Hval := ConcreteCategory.congr_hom Hring
    ⟨x, IntermediateField.mem_adjoin_simple_self k x⟩
  change g x = x at Hval
  simpa only [AlgEquiv.one_apply] using Hval

end FiniteEtale

end AlgebraicGeometry
