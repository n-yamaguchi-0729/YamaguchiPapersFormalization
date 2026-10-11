/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.ConnectedActions
import EtaleFundamentalGroups.GaloisCategories.Functoriality
import EtaleFundamentalGroups.GeometricFiber.PointedCover
import EtaleFundamentalGroups.FiniteEtale.Connected
import Mathlib.CategoryTheory.Galois.Equivalence

/-!
# Actual finite étale covers for arbitrary open subgroups

The quotient action of an arbitrary open subgroup is realized by a connected
object, with no normality assumption and no restriction on the fiber universe.
For a scheme this gives a pointed connected finite étale cover whose fundamental
group is the specified subgroup. The inclusion is the actual homomorphism
induced by the covering morphism.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u₁ u₂ w

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]

private theorem exists_connected_object_point_stabilizer_eq
    (F : C ⥤ FintypeCat.{u₁}) [FiberFunctor F]
    (U : OpenSubgroup (Aut F)) :
    ∃ (X : C) (_ : IsConnected X) (x : F.obj X),
      MulAction.stabilizer (Aut F) x = (U : Subgroup (Aut F)) := by
  obtain ⟨X, ⟨e⟩⟩ := exists_lift_of_quotient_openSubgroup (F := F) U
  let ef : F.obj X ≅ FintypeCat.of (Aut F ⧸ (U : Subgroup (Aut F))) :=
    (forget₂ (Action FintypeCat (Aut F)) FintypeCat).mapIso e
  let q : Aut F ⧸ (U : Subgroup (Aut F)) := QuotientGroup.mk (1 : Aut F)
  let x : F.obj X := ef.inv q
  have : Nonempty (F.obj X) := ⟨x⟩
  have : MulAction.IsPretransitive (Aut F) (F.obj X) := by
    constructor
    intro a b
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Aut F) (ef.hom a) (ef.hom b)
    refine ⟨g, (ConcreteCategory.bijective_of_isIso ef.hom).injective ?_⟩
    exact (ConcreteCategory.congr_hom (e.hom.comm g) a).trans hg
  refine ⟨X, FiberFunctor.isConnected_of_isPretransitive F X, x, ?_⟩
  ext g
  rw [← MulAction.stabilizer_quotient (U : Subgroup (Aut F))]
  change g • x = x ↔ g • q = q
  have hx : ef.hom x = q := FintypeCat.inv_hom_id_apply ef q
  have he : ef.hom (g • x) = g • ef.hom x :=
    ConcreteCategory.congr_hom (e.hom.comm g) x
  constructor
  · intro hg
    exact (congrArg (g • ·) hx).symm.trans
      (he.symm.trans ((congrArg ef.hom.hom hg).trans hx))
  · intro hg
    apply (ConcreteCategory.bijective_of_isIso ef.hom).injective
    exact he.trans ((congrArg (g • ·) hx).trans (hg.trans hx.symm))

/-- Every open subgroup is the stabilizer of a point of a connected object,
even when the fiber functor and its source category have different universes. -/
theorem exists_connected_object_point_stabilizer_eq_any_universe
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (U : OpenSubgroup (Aut F)) :
    ∃ (X : C) (_ : IsConnected X) (x : F.obj X),
      MulAction.stabilizer (Aut F) x = (U : Subgroup (Aut F)) := by
  let F' : C ⥤ FintypeCat.{u₁} := F ⋙ FintypeCat.uSwitch.{w, u₁}
  let : FiberFunctor F' := FiberFunctor.comp_right _
  let eF : Aut F ≃ₜ* Aut F' :=
    autEquivAutWhiskerRight F
      (FintypeCat.uSwitchEquivalence.{w, u₁}).fullyFaithfulFunctor
  let U' : OpenSubgroup (Aut F') :=
    U.comap eF.symm.toMonoidHom eF.symm.continuous
  obtain ⟨X, hX, x', hx'⟩ := exists_connected_object_point_stabilizer_eq F' U'
  let eX : F'.obj X ≃ F.obj X := FintypeCat.uSwitchEquiv (F.obj X)
  refine ⟨X, hX, eX x', ?_⟩
  ext g
  change g • eX x' = eX x' ↔ g ∈ (U : Subgroup (Aut F))
  have he : eX ((eF g) • x') = g • eX x' := by
    change (F.obj X).uSwitchEquiv
        (FintypeCat.uSwitch.map (g.hom.app X) x') =
      g.hom.app X ((F.obj X).uSwitchEquiv x')
    exact (FintypeCat.uSwitchEquiv_naturality (g.hom.app X) x').symm
  calc
    g • eX x' = eX x' ↔ (eF g) • x' = x' := by
      rw [← he]
      exact eX.injective.eq_iff
    _ ↔ eF g ∈ MulAction.stabilizer (Aut F') x' :=
      MulAction.mem_stabilizer_iff.symm
    _ ↔ eF g ∈ (U' : Subgroup (Aut F')) := by rw [hx']
    _ ↔ g ∈ (U : Subgroup (Aut F)) := by
      change eF.symm (eF g) ∈ U ↔ g ∈ U
      rw [eF.symm_apply_apply]

end CategoryTheory.PreGaloisCategory

universe u

open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} [ConnectedSpace S]
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- Every open subgroup is the fundamental group of an actual connected finite
étale cover. The equivalence identifies subgroup inclusion with the actual
homomorphism on fundamental groups induced by the covering map. -/
theorem exists_connectedCover_lift_fundamentalGroup_equiv_openSubgroup
    (xi : Spec (.of Ω) ⟶ S) (U : OpenSubgroup π₁ᵉᵗ(xi)) :
    ∃ (A : FiniteEtale S) (_ : ConnectedSpace A.left)
      (xi' : Spec (.of Ω) ⟶ A.left) (hxi : xi' ≫ A.hom = xi)
      (e : π₁ᵉᵗ(xi') ≃ₜ* U),
      ∀ a : π₁ᵉᵗ(xi'), (e a : π₁ᵉᵗ(xi)) =
        hxi ▸ fundamentalGroupHom A.hom xi' a := by
  obtain ⟨A, hA, x, hx⟩ :=
    exists_connected_object_point_stabilizer_eq_any_universe (fiber xi) U
  have : IsConnected A := hA
  let z : Over.mk xi ⟶ A.toComma := fiberObjEquivHom xi A x
  let xi' : Spec (.of Ω) ⟶ A.left := z.left
  have hxi : xi' ≫ A.hom = xi := z.w
  let H : Subgroup π₁ᵉᵗ(xi) :=
    hxi ▸ MulAction.stabilizer π₁ᵉᵗ(xi' ≫ A.hom)
      (liftedFiberPointOverComposite A xi')
  have hlift : (fiberObjEquivHom xi A).symm (Over.homMk xi' hxi) = x := by
    apply (fiberObjEquivHom xi A).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have hH : H = (U : Subgroup π₁ᵉᵗ(xi)) := by
    dsimp only [H]
    rw [transported_stabilizer_liftedFiberPointOverComposite A xi' hxi, hlift, hx]
  let e := fundamentalGroupEquivStabilizerOfLiftOfEq A xi' hxi
  have he (a : π₁ᵉᵗ(xi')) : (e a : π₁ᵉᵗ(xi)) =
      hxi ▸ fundamentalGroupHom A.hom xi' a :=
    fundamentalGroupEquivStabilizerOfLiftOfEq_coe A xi' hxi a
  change (hxi ▸ MulAction.stabilizer π₁ᵉᵗ(xi' ≫ A.hom)
    (liftedFiberPointOverComposite A xi')) = U.toSubgroup at hH
  refine ⟨A, connectedSpace_left_of_isConnected A, xi', hxi, ?_⟩
  change ∃ e' : π₁ᵉᵗ(xi') ≃ₜ* ↥U.toSubgroup,
    ∀ a : π₁ᵉᵗ(xi'), (e' a : π₁ᵉᵗ(xi)) = hxi ▸ fundamentalGroupHom A.hom xi' a
  rw [← hH]
  exact ⟨e, he⟩

end AlgebraicGeometry.FiniteEtale
