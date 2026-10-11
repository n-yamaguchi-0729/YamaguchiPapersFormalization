/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.FinitePresentationHomBaseChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Flat base change for `Ext¹` from a finitely presented module

Over a noetherian ring, the first syzygy of a finitely presented module is
again finitely presented.  The contravariant long exact `Ext` sequence of a
finite-free presentation therefore expresses `Ext¹` as a cokernel of two
`Hom` modules to which finite-presentation base change applies.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra ChangeOfRings

namespace EtaleFundamentalGroups

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private theorem extendScalarsTensorAlgebra_eq :
    ((algebraMap S S).comp (algebraMap R S)).toAlgebra =
      (inferInstance : Algebra R S) := by
  apply Algebra.algebra_ext
  intro r
  simp [RingHom.algebraMap_toAlgebra]

private theorem extendScalarsTensorModule_eq :
    ((ModuleCat.restrictScalars (algebraMap R S)).obj
        (ModuleCat.of S S)).isModule =
      (@Algebra.toModule R S _ _ (inferInstance : Algebra R S)) := by
  apply Module.ext'
  intro r s
  change algebraMap R S r • (show S from s) =
    r • (show S from s)
  exact IsScalarTower.algebraMap_smul S r (show S from s)

private noncomputable def extendScalarsTensorEquiv (Q : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj Q ≃ₗ[S] S ⊗[R] Q := by
  letI : SMulCommClass R S
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) :=
    ModuleCat.sMulCommClass_mk (algebraMap R S) S
  change (((ModuleCat.restrictScalars (algebraMap R S)).obj
    (ModuleCat.of S S)) ⊗[R] Q) ≃ₗ[S] S ⊗[R] Q
  let e : ((ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) ≃ₗ[R] S :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change algebraMap R S r * (show S from x) = r • (show S from x)
        exact (Algebra.smul_def r (show S from x)).symm }
  let eT := TensorProduct.congr e (LinearEquiv.refl R Q)
  refine { eT.toAddEquiv with map_smul' := ?_ }
  intro s x
  change eT (s • x) = s • eT x
  induction x using TensorProduct.inductionOn with
  | tmul s' q =>
      simp only [eT, TensorProduct.smul_tmul', TensorProduct.congr_tmul,
        LinearEquiv.refl_apply]
      rfl
  | add x y hx hy =>
      rw [TensorProduct.smul_add, map_add, hx, hy, map_add, smul_add]

private theorem extendScalarsTensorEquiv_tmul (Q : ModuleCat.{u} R) (s : S) (q : Q) :
    extendScalarsTensorEquiv (S := S) Q
        (show (ModuleCat.extendScalars (algebraMap R S)).obj Q from
          s ⊗ₜ[R,algebraMap R S] q) = s ⊗ₜ[R] q := by
  rfl

private theorem extendScalarsTensorEquiv_symm_tmul (Q : ModuleCat.{u} R) (s : S) (q : Q) :
    (extendScalarsTensorEquiv (S := S) Q).symm (s ⊗ₜ[R] q) =
      (show (ModuleCat.extendScalars (algebraMap R S)).obj Q from
        s ⊗ₜ[R,algebraMap R S] q) := by
  apply (extendScalarsTensorEquiv (S := S) Q).injective
  rw [LinearEquiv.apply_symm_apply, extendScalarsTensorEquiv_tmul]

/-- Extension of scalars is linear over the base ring when the target module
category is equipped with its restriction-of-scalars linear structure. -/
noncomputable local instance moduleCatExtendScalarsLinearOverBase :
    (ModuleCat.extendScalars (algebraMap R S)).Linear R where
  map_smul f r := by
    apply ModuleCat.hom_injective
    dsimp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      ModuleCat.hom_ofHom]
    let : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
    exact LinearMap.baseChange_smul r f.hom

/-- Flat extension of scalars preserves finite limits.  This instance is
the exactness input needed by the functorial map on `Ext`. -/
noncomputable local instance moduleCatExtendScalarsPreservesFiniteLimits
    [Module.Flat R S] :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)

/-- A flat extension-of-scalars functor is additive. -/
noncomputable local instance moduleCatExtendScalarsAdditive [Module.Flat R S] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).Additive :=
  (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).additive_of_preserves_binary_products

/-- The `R`-action on an `Ext` group of `S`-modules obtained from the
restriction-of-scalars linear category structure is compatible with its
native `S`-action. -/
noncomputable local instance extIsScalarTowerOfAlgebra
    (X Y : ModuleCat.{u} S) (i : ℕ) :
    IsScalarTower R S (Ext X Y i) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simp only [Ext.smul_eq_comp_mk₀]
    congr 2

variable [Small.{u} R] [Small.{u} S] [Module.Flat R S]

private theorem extendScalars_mapExtZero_isBaseChange
    (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q] :
    IsBaseChange S
      ((ModuleCat.extendScalars (algebraMap R S)).mapExtLinearMap
        R Q N 0) := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let eR : Ext Q N 0 ≃ₗ[R] (Q →ₗ[R] N) :=
    (Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv
  let eS : Ext (F.obj Q) (F.obj N) 0 ≃ₗ[S]
      (F.obj Q →ₗ[S] F.obj N) :=
    (Ext.linearEquiv₀ (R := S)).trans ModuleCat.homLinearEquiv
  let hExt := F.mapExtLinearMap R Q N 0
  let hHom : (Q →ₗ[R] N) →ₗ[R] (F.obj Q →ₗ[S] F.obj N) :=
    by
      letI : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
      change (Q →ₗ[R] N) →ₗ[R] ((S ⊗[R] Q) →ₗ[S] (S ⊗[R] N))
      exact LinearMap.baseChangeHom R S Q N
  have hcomm : hHom.comp eR.toLinearMap =
      (eS.restrictScalars R).comp hExt := by
    let : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
    apply LinearMap.ext
    intro x
    have hx := congrFun (Ext.mapExactFunctor₀ F Q N) x
    have hx' := congrArg
      (Ext.homEquiv₀ (X := F.obj Q) (Y := F.obj N)) hx
    have hx'' := congrArg ModuleCat.Hom.hom hx'
    change (LinearMap.baseChangeHom R S Q N) (eR x) = eS (hExt x)
    change (F.map (Ext.homEquiv₀ x)).hom =
      (Ext.homEquiv₀ (Ext.mapExactFunctor F x)).hom
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx''.symm
  have hbcHom : IsBaseChange S hHom := by
    let eQ := extendScalarsTensorEquiv (S := S) Q
    let eN := extendScalarsTensorEquiv (S := S) N
    let eHom : (F.obj Q →ₗ[S] F.obj N) ≃ₗ[S]
        ((S ⊗[R] Q) →ₗ[S] (S ⊗[R] N)) :=
      LinearEquiv.arrowCongr eQ eN
    have hcommHom :
        (LinearMap.baseChangeHom R S Q N).comp
            (LinearEquiv.refl R (Q →ₗ[R] N)).toLinearMap =
          (eHom.restrictScalars R).toLinearMap.comp hHom := by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro x
      change f.baseChange S x = eN (hHom f (eQ.symm x))
      induction x using TensorProduct.inductionOn with
      | tmul s q =>
          rw [LinearMap.baseChange_tmul]
          dsimp only [eQ]
          rw [extendScalarsTensorEquiv_symm_tmul]
          have hf : hHom f
              (show F.obj Q from s ⊗ₜ[R,algebraMap R S] q) =
            (show F.obj N from s ⊗ₜ[R,algebraMap R S] (f q)) := by
            rfl
          rw [hf]
          exact (extendScalarsTensorEquiv_tmul N s (f q)).symm
      | add x y hx hy =>
          rw [map_add, map_add, map_add, map_add, hx, hy]
    exact (IsBaseChange.iff_of_equiv_comm
      (LinearEquiv.refl R (Q →ₗ[R] N)) eHom hcommHom).mpr
        (linearMap_baseChangeHom_isBaseChange_of_finitePresentation_of_flat
          (R := R) (S := S) (M := Q) (N := N))
  exact (IsBaseChange.iff_of_equiv_comm eR eS hcomm).mpr hbcHom

private theorem ext_precomp_extClass_exact
    {T : ShortComplex (ModuleCat.{u} R)} (hT : T.ShortExact)
    (N : ModuleCat.{u} R) :
    Function.Exact
      ((Ext.mk₀ T.f).precompOfLinear R N (zero_add 0))
      (hT.extClass.precompOfLinear R N (Nat.add_zero 1)) := by
  change Function.Exact
    ((Ext.mk₀ T.f).precomp N (zero_add 0))
    (hT.extClass.precomp N (Nat.add_zero 1))
  have h := (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.contravariant_sequence_exact₁' hT N 0 1 (by omega))
  intro x
  simpa only [AddCommGrpCat.hom_ofHom] using h x

private theorem ext_precomp_extClass_surjective_of_projective
    {T : ShortComplex (ModuleCat.{u} R)} (hT : T.ShortExact)
    (N : ModuleCat.{u} R) [Projective T.X₂] :
    Function.Surjective
      (hT.extClass.precompOfLinear R N (Nat.add_zero 1)) := by
  change Function.Surjective
    (hT.extClass.precomp N (Nat.add_zero 1))
  simpa only using
    (precomp_extClass_surjective_of_projective_X₂ N hT 0)

/-- For a flat algebra over a noetherian ring, the functorial map on
`Ext¹` from a finitely presented first variable is a base-change map. -/
theorem mapExtOne_isBaseChange_of_finitePresentation_of_flat
    [IsNoetherianRing R]
    (Q N : ModuleCat.{u} R) [Module.FinitePresentation R Q] :
    IsBaseChange S
      ((ModuleCat.extendScalars (algebraMap R S)).mapExtLinearMap
        R Q N 1) := by
  let E := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  obtain ⟨F, _, _, _, _, p, hp⟩ := Module.exists_finite_presentation R Q
  let : Module.Finite R (LinearMap.ker p) :=
    Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker p hp)
  let : Module.FinitePresentation R (LinearMap.ker p) :=
    Module.finitePresentation_of_finite R (LinearMap.ker p)
  let : Module.FinitePresentation R F :=
    Module.finitePresentation_of_projective R F
  let T := p.shortComplexKer
  let : Module.FinitePresentation R T.X₁ := by
    dsimp [T, LinearMap.shortComplexKer]
    infer_instance
  let : Module.FinitePresentation R T.X₂ := by
    dsimp [T, LinearMap.shortComplexKer]
    infer_instance
  let : Module.Free R T.X₂ := by
    dsimp [T, LinearMap.shortComplexKer]
    infer_instance
  have hT : T.ShortExact := LinearMap.shortExact_shortComplexKer hp
  let T' := T.map E
  have hT' : T'.ShortExact := hT.map_of_exact E
  let f : Ext T.X₂ N 0 →ₗ[R] Ext T.X₁ N 0 :=
    (Ext.mk₀ T.f).precompOfLinear R N rfl
  let d : Ext T.X₁ N 0 →ₗ[R] Ext T.X₃ N 1 :=
    hT.extClass.precompOfLinear R N rfl
  let f' : Ext T'.X₂ (E.obj N) 0 →ₗ[S] Ext T'.X₁ (E.obj N) 0 :=
    (Ext.mk₀ T'.f).precompOfLinear S (E.obj N) rfl
  let d' : Ext T'.X₁ (E.obj N) 0 →ₗ[S] Ext T'.X₃ (E.obj N) 1 :=
    hT'.extClass.precompOfLinear S (E.obj N) rfl
  let h₁ := E.mapExtLinearMap R T.X₂ N 0
  let h₂ := E.mapExtLinearMap R T.X₁ N 0
  let h₃ := E.mapExtLinearMap R T.X₃ N 1
  have hbc₁ : IsBaseChange S h₁ :=
    extendScalars_mapExtZero_isBaseChange (S := S) T.X₂ N
  have hbc₂ : IsBaseChange S h₂ :=
    extendScalars_mapExtZero_isBaseChange (S := S) T.X₁ N
  have hcomm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁ := by
    ext x
    change ((Ext.mk₀ T.f).comp x rfl).mapExactFunctor E =
      (Ext.mk₀ (E.map T.f)).comp (x.mapExactFunctor E) rfl
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  have hcomm₂ : h₃.comp d = (d'.restrictScalars R).comp h₂ := by
    ext x
    change (hT.extClass.comp x rfl).mapExactFunctor E =
      hT'.extClass.comp (x.mapExactFunctor E) rfl
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  have hexact : Function.Exact f d :=
    ext_precomp_extClass_exact hT N
  have hsurj : Function.Surjective d :=
    ext_precomp_extClass_surjective_of_projective hT N
  let : Module.Free S T'.X₂ := by
    change Module.Free S (E.obj T.X₂)
    dsimp [E, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj']
    let : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
    change Module.Free S (S ⊗[R] T.X₂)
    infer_instance
  have hexact' : Function.Exact f' d' :=
    ext_precomp_extClass_exact hT' (E.obj N)
  have hsurj' : Function.Surjective d' :=
    ext_precomp_extClass_surjective_of_projective hT' (E.obj N)
  have hbc₃ : IsBaseChange S h₃ :=
    IsBaseChange.of_right_exact S h₁ h₂ h₃
      hcomm₁ hcomm₂ hbc₁ hbc₂
      hexact hsurj hexact' hsurj'
  simpa only [h₃, T, LinearMap.shortComplexKer] using hbc₃

end EtaleFundamentalGroups

end
