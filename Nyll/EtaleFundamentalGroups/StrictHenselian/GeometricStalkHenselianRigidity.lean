/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Nyll.SchemeTheory.Affine.SpecSectionMap
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Rigidity of the actual map to a strictly Henselian target

An endomorphism of the target that preserves the base map and its residue
map fixes every actual pointed-neighborhood lift. Naturality of global
sections then fixes their section maps, and the defining presheaf-fiber
colimit fixes the constructed ring homomorphism.

No normalization comparison, inertia action, or fixed-image identification
is assumed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing S]
  [IsSepClosed (IsLocalRing.ResidueField S)] (f : R →+* S)

/-- Precomposing an actual pointed lift with a base-preserving,
residue-trivial target endomorphism leaves that lift unchanged. -/
theorem geometricNeighborhoodHenselianLift_comp_endomorphism
    (τ : S →+* S) (hbase : τ.comp f = f)
    (hresidue : (IsLocalRing.residue S).comp τ = IsLocalRing.residue S)
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    Spec.map (CommRingCat.ofHom τ) ≫ geometricNeighborhoodHenselianLift f W t =
      geometricNeighborhoodHenselianLift f W t := by
  apply (Etale.existsUnique_lift_of_henselianLocalRing S W.hom
    (Spec.map (CommRingCat.ofHom f)) t.left
    (t.w.trans (Spec.map_comp (CommRingCat.ofHom f)
      (CommRingCat.ofHom (IsLocalRing.residue S))))).unique
  · constructor
    · calc
        (Spec.map (CommRingCat.ofHom τ) ≫ geometricNeighborhoodHenselianLift f W t) ≫
            W.hom = Spec.map (CommRingCat.ofHom τ) ≫
              (geometricNeighborhoodHenselianLift f W t ≫ W.hom) := Category.assoc _ _ _
        _ = Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom f) :=
          congrArg (fun k : Spec (.of S) ⟶ Spec (.of R) =>
            Spec.map (CommRingCat.ofHom τ) ≫ k)
            (geometricNeighborhoodHenselianLift_comp f W t)
        _ = Spec.map (CommRingCat.ofHom (τ.comp f)) :=
          (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom τ)).symm
        _ = Spec.map (CommRingCat.ofHom f) :=
          congrArg (fun g : R →+* S => Spec.map (CommRingCat.ofHom g)) hbase
    · have hresidueCat :
          (CommRingCat.ofHom τ : CommRingCat.of S ⟶ CommRingCat.of S) ≫
              CommRingCat.ofHom (IsLocalRing.residue S) =
            CommRingCat.ofHom (IsLocalRing.residue S) :=
        CommRingCat.hom_ext hresidue
      have hresidueSpec :
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
              Spec.map (CommRingCat.ofHom τ) =
            Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) :=
        (Spec.map_comp (CommRingCat.ofHom τ)
          (CommRingCat.ofHom (IsLocalRing.residue S))).symm.trans
          (congrArg (fun g : CommRingCat.of S ⟶
            CommRingCat.of (IsLocalRing.ResidueField S) => Spec.map g) hresidueCat)
      have hpoint :
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
              (Spec.map (CommRingCat.ofHom τ) ≫ geometricNeighborhoodHenselianLift f W t) =
            Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
              geometricNeighborhoodHenselianLift f W t :=
        (Category.assoc (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)))
          (Spec.map (CommRingCat.ofHom τ))
          (geometricNeighborhoodHenselianLift f W t)).symm.trans
          (congrArg (fun k : Spec (.of (IsLocalRing.ResidueField S)) ⟶ Spec (.of S) =>
            k ≫ geometricNeighborhoodHenselianLift f W t) hresidueSpec)
      have hlift :
          Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
              geometricNeighborhoodHenselianLift f W t =
            (t.left : Spec (.of (IsLocalRing.ResidueField S)) ⟶ W.left) :=
        geometricNeighborhoodHenselianLift_residue f W t
      exact hpoint.trans hlift
  · exact ⟨geometricNeighborhoodHenselianLift_comp f W t,
      geometricNeighborhoodHenselianLift_residue f W t⟩

private theorem geometricStalkGerm_henselian_comp_endomorphism
    (τ : S →+* S) (hbase : τ.comp f = f)
    (hresidue : (IsLocalRing.residue S).comp τ = IsLocalRing.residue S)
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    (geometricStalkGerm (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))) W t ≫
        CommRingCat.ofHom (geometricStalkToHenselian f)) ≫ CommRingCat.ofHom τ =
      geometricStalkGerm (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))) W t ≫
        CommRingCat.ofHom (geometricStalkToHenselian f) := by
  let γ : Γ(W.left, ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) W t
  let m : geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (geometricStalkToHenselian f)
  let l : Spec (.of S) ⟶ W.left := geometricNeighborhoodHenselianLift f W t
  have hγ : γ ≫ m = specLiftSectionMap l :=
    geometricStalkGerm_toSpecLiftSectionMap f W t
  change (γ ≫ m) ≫ CommRingCat.ofHom τ = γ ≫ m
  calc
    (γ ≫ m) ≫ CommRingCat.ofHom τ = specLiftSectionMap l ≫ CommRingCat.ofHom τ :=
      congrArg (fun k : Γ(W.left, ⊤) ⟶ CommRingCat.of S => k ≫ CommRingCat.ofHom τ) hγ
    _ = specLiftSectionMap l :=
      specLiftSectionMap_comp_endomorphism l τ
        (geometricNeighborhoodHenselianLift_comp_endomorphism f τ hbase hresidue W t)
    _ = γ ≫ m := hγ.symm

/-- The actual geometric-stalk map is fixed by every target endomorphism
that preserves its base map and acts trivially after reduction. -/
theorem geometricStalkToHenselian_comp_endomorphism
    (τ : S →+* S) (hbase : τ.comp f = f)
    (hresidue : (IsLocalRing.residue S).comp τ = IsLocalRing.residue S) :
    τ.comp (geometricStalkToHenselian f) = geometricStalkToHenselian f := by
  apply RingHom.ext
  intro a
  obtain ⟨W, t, z, rfl⟩ := geometricStalk_exists_representative
    (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) a
  exact ConcreteCategory.congr_hom
    (geometricStalkGerm_henselian_comp_endomorphism f τ hbase hresidue W t) z

end EtaleFundamentalGroups.StrictHenselian
