/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CechTensorCoefficients
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionSum
import Nyll.EtaleFundamentalGroups.Purity.IdealPowerTorsionInjective
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationHomotopy
import Nyll.EtaleFundamentalGroups.Purity.PrincipalLocalizationTensorCoefficients
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Contraction of the Čech complex on injectives

The actual principal localization contraction is tensored with the
remaining factors. Iteration identifies the Čech complex of an injective
module with its ideal-power torsion, concentrated in degree zero.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R]

/-- Tensoring a homotopy equivalence on the left preserves it. -/
def tensorLeftHomotopyEquiv
    {K L : CochainComplex (ModuleCat.{u} R) ℕ}
    (e : HomotopyEquiv K L) (B : CochainComplex (ModuleCat.{u} R) ℕ) :
    HomotopyEquiv (HomologicalComplex.tensorObj K B)
      (HomologicalComplex.tensorObj L B) := by
  let F := ((curriedTensor (ModuleCat.{u} R)).map₂HomologicalComplex
    (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).flip.obj B
  refine
    { hom := F.map e.hom
      inv := F.map e.inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · change Homotopy (F.map e.hom ≫ F.map e.inv) (𝟙 (F.obj K))
    rw [← F.map_comp, ← F.map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyHomInvId
      (𝟙 B) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)
  · change Homotopy (F.map e.inv ≫ F.map e.hom) (𝟙 (F.obj L))
    rw [← F.map_comp, ← F.map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyInvHomId
      (𝟙 B) (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℕ)

/-- The empty-list contraction is formed at the coefficient-module
level before any primary-component module is substituted. -/
def cechNilHomotopyEquiv (M N : ModuleCat.{u} R) (e : M ≅ N) :
    HomotopyEquiv
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechLocalizationComplex ([] : List R)))
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj N) :=
  HomotopyEquiv.ofIso
    ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft M)
        (ComplexShape.up ℕ) 0).app (𝟙_ (ModuleCat.{u} R)) ≪≫
      (CochainComplex.single₀ (ModuleCat.{u} R)).mapIso ((ρ_ M) ≪≫ e))

/-- The inverse empty-list contraction is the coefficient comparison
followed by the inverse unit map in degree zero. -/
theorem cechNilHomotopyEquiv_inv_f_zero (M N : ModuleCat.{u} R) (e : M ≅ N) :
    (cechNilHomotopyEquiv M N e).inv.f 0 = e.inv ≫ (ρ_ M).inv := by
  change (((CochainComplex.single₀ (ModuleCat.{u} R)).map (e.inv ≫ (ρ_ M).inv)) ≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorLeft M)
      (ComplexShape.up ℕ) 0).inv.app (𝟙_ (ModuleCat.{u} R))).f 0 = _
  rw [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  change (e.inv ≫ (ρ_ M).inv) ≫ 𝟙 (M ⊗ 𝟙_ (ModuleCat.{u} R)) ≫
    (M ◁ 𝟙 (𝟙_ (ModuleCat.{u} R))) = _
  rw [whiskerLeft_id, Category.id_comp, Category.comp_id]

private def fullSubmoduleIso (M : ModuleCat.{u} R)
    (N : Submodule R M) (hN : N = ⊤) : M ≅ ModuleCat.of R N :=
  (LinearEquiv.ofBijective N.subtype
    ⟨N.subtype_injective, fun m => ⟨⟨m, hN.symm ▸ Submodule.mem_top⟩, rfl⟩⟩).symm.toModuleIso

private theorem fullSubmoduleIso_inv (M : ModuleCat.{u} R)
    (N : Submodule R M) (hN : N = ⊤) :
    (fullSubmoduleIso M N hN).inv = ModuleCat.ofHom N.subtype := rfl

/-- Empty-support torsion is the whole module. Its inverse is constructed
as the actual subtype map, avoiding transport through equal submodules. -/
def cechNilTorsionIso (M : ModuleCat.{u} R) :
    M ≅ ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList ([] : List R))) := by
  apply fullSubmoduleIso
  apply top_unique
  intro m _
  rw [Ideal.ofList_nil]
  apply (Ideal.primaryComponent_mem (I := (⊥ : Ideal R)) (M := M) m).mpr
  refine ⟨1, ?_⟩
  rw [pow_one, Submodule.mem_torsionBySet_iff]
  intro a
  rw [show (a : R) = 0 from a.property, zero_smul]

/-- The inverse empty-support identification is the specified inclusion. -/
theorem cechNilTorsionIso_inv (M : ModuleCat.{u} R) :
    (cechNilTorsionIso M).inv =
      ModuleCat.ofHom (Ideal.primaryComponent M (Ideal.ofList ([] : List R))).subtype := by
  unfold cechNilTorsionIso
  exact fullSubmoduleIso_inv M _ _

/-- The finite Čech complex with injective coefficients contracts to
power torsion for the ideal generated by its list. -/
def cechInjectiveHomotopyEquiv [IsNoetherianRing R]
    (xs : List R) (M : ModuleCat.{u} R) [Module.Injective R M] :
    HomotopyEquiv
      (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cechLocalizationComplex xs))
      ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList xs)))) := by
  induction xs generalizing M with
  | nil =>
      exact cechNilHomotopyEquiv M
        (ModuleCat.of R (Ideal.primaryComponent M (Ideal.ofList ([] : List R))))
        (cechNilTorsionIso M)
  | cons x xs ih =>
      let A := principalLocalizationComplex x (ModuleCat.of R R)
      let B := cechLocalizationComplex xs
      let S := (CochainComplex.single₀ (ModuleCat.{u} R)).obj M
      let T := ModuleCat.of R (Ideal.primaryComponent M (Ideal.span {x}))
      letI : Module.Injective R T := moduleInjective_primaryComponent (Ideal.span {x}) M
      let e : HomotopyEquiv (HomologicalComplex.tensorObj S A)
          ((CochainComplex.single₀ (ModuleCat.{u} R)).obj T) :=
        ((HomotopyEquiv.ofIso (singleTensorComplexIso M A).symm).trans
          (HomotopyEquiv.ofIso (principalLocalizationTensorCoefficientsIso x M))).trans
          (principalLocalizationHomotopyEquiv x M).symm
      let h : HomotopyEquiv (HomologicalComplex.tensorObj
          ((CochainComplex.single₀ (ModuleCat.{u} R)).obj T) B)
          ((CochainComplex.single₀ (ModuleCat.{u} R)).obj
            (ModuleCat.of R (Ideal.primaryComponent T (Ideal.ofList xs)))) :=
        (HomotopyEquiv.ofIso (singleTensorComplexIso T B).symm).trans (ih T)
      let q : Ideal.primaryComponent T (Ideal.ofList xs) ≃ₗ[R]
          Ideal.primaryComponent M (Ideal.ofList (x :: xs)) :=
        (primaryComponentIteratedLinearEquiv M (Ideal.span {x}) (Ideal.ofList xs)).trans
          (LinearEquiv.ofEq _ _ (congrArg
            (fun I : Ideal R => Ideal.primaryComponent M I) (Ideal.ofList_cons x xs).symm))
      exact (HomotopyEquiv.ofIso
        (singleTensorComplexIso M (cechLocalizationComplex (x :: xs)))).trans
        ((HomotopyEquiv.ofIso (HomologicalComplex.associator S A B).symm).trans
          ((tensorLeftHomotopyEquiv e B).trans
            (h.trans (HomotopyEquiv.ofIso
              ((CochainComplex.single₀ (ModuleCat.{u} R)).mapIso q.toModuleIso)))))

/-- Positive Čech cohomology vanishes on injective modules. -/
theorem cechInjective_exactAt_succ [IsNoetherianRing R]
    (xs : List R) (M : ModuleCat.{u} R) [Module.Injective R M] (n : ℕ) :
    (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cechLocalizationComplex xs)).ExactAt (n + 1) := by
  let e := cechInjectiveHomotopyEquiv xs M
  apply (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
  apply HomologicalComplex.ExactAt.of_isZero
  exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)

end EtaleFundamentalGroups.Purity

end
