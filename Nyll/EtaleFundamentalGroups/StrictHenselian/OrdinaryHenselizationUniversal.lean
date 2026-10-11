/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselization
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkChangeField
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Etale

/-!
# The universal property of the constructed ordinary henselization

For a local map `A → S` into a Henselian local ring, extend every neighborhood
point along `κ(A) → κ(S)` and use the existing Henselian neighborhood lifts.
Their already constructed colimit map gives the universal map `H(A) → S`.

Local maps with the same base map have the same residue map, because
`κ(H(A)) = κ(A)`. On an affine pointed neighborhood, uniqueness of the actual
Henselian étale lift then makes their section maps equal. Every germ admits
such an affine refinement, proving uniqueness on the original colimit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {A S : Type u} [CommRing A] [IsLocalRing A]
  [CommRing S] [HenselianLocalRing S] (f : A →+* S) [IsLocalHom f]

/-- The actual local map out of the residue-pointed étale colimit. -/
def ordinaryHenselizationLift : ordinaryHenselization A →+* S :=
  (geometricStalkToHenselian f).comp
    (geometricStalkChangeField (IsLocalRing.residue A)
      (IsLocalRing.ResidueField.map f)).hom

instance ordinaryHenselizationLift_isLocalHom :
    IsLocalHom (ordinaryHenselizationLift f) where
  map_nonunit a ha :=
    (geometricStalkChangeField_isLocalHom (IsLocalRing.residue A)
      (IsLocalRing.ResidueField.map f)).map_nonunit a
        ((geometricStalkToHenselian_isLocalHom f).map_nonunit _ ha)

/-- The universal map extends the specified original local ring map. -/
theorem ordinaryHenselizationLift_comp_map :
    (ordinaryHenselizationLift f).comp (ordinaryHenselizationMap A) = f := by
  let G : CommRingCat.{u} := geometricStalk
    (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f)))
  let i : ordinaryHenselization A →+* G :=
    (geometricStalkChangeField (IsLocalRing.residue A)
      (IsLocalRing.ResidueField.map f)).hom
  let j : A →+* ordinaryHenselization A := ordinaryHenselizationMap A
  let k : A →+* G := geometricStalkStructureMap ((IsLocalRing.residue S).comp f)
  have hij : i.comp j = k := geometricStalkChangeField_comp_structure
    (IsLocalRing.residue A) (IsLocalRing.ResidueField.map f)
  calc
    (ordinaryHenselizationLift f).comp j =
        (geometricStalkToHenselian f).comp (i.comp j) :=
      RingHom.comp_assoc j i (geometricStalkToHenselian f)
    _ = (geometricStalkToHenselian f).comp k :=
      congrArg (fun q : A →+* G => (geometricStalkToHenselian f).comp q) hij
    _ = f := geometricStalkToHenselian_comp_structure f

/-- Localness and the original base map determine the residue of every map
out of the ordinary henselization. -/
theorem ordinaryHenselization_localMap_residue
    (g : ordinaryHenselization A →+* S) [IsLocalHom g]
    (hg : g.comp (ordinaryHenselizationMap A) = f) :
    (IsLocalRing.residue S).comp g = (IsLocalRing.ResidueField.map f).comp
      (geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).hom := by
  apply RingHom.ext
  intro a
  let s : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let ε : ordinaryHenselization A →+* IsLocalRing.ResidueField A :=
    (geometricStalkEvaluation s).hom
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := A) (ε a)
  have hεr : ε (ordinaryHenselizationMap A r) = IsLocalRing.residue A r :=
    geometricStalkStructureMap_evaluation_apply (IsLocalRing.residue A) r
  have hzero : ε (a - ordinaryHenselizationMap A r) = 0 := by
    rw [map_sub, hεr, hr, sub_self]
  have hmem : a - ordinaryHenselizationMap A r ∈
      IsLocalRing.maximalIdeal (ordinaryHenselization A) :=
    (geometricStalk_mem_maximalIdeal_iff s _).mpr hzero
  have heq : IsLocalRing.residue S (g a) =
      IsLocalRing.residue S (g (ordinaryHenselizationMap A r)) := by
    have hz := (IsLocalRing.residue_eq_zero_iff
      (g (a - ordinaryHenselizationMap A r))).mpr (map_nonunit g _ hmem)
    rw [map_sub, map_sub, sub_eq_zero] at hz
    exact hz
  change IsLocalRing.residue S (g a) =
    IsLocalRing.ResidueField.map f (ε a)
  calc
    IsLocalRing.residue S (g a) =
        IsLocalRing.residue S (g (ordinaryHenselizationMap A r)) := heq
    _ = IsLocalRing.residue S (f r) :=
      congrArg (IsLocalRing.residue S) (RingHom.congr_fun hg r)
    _ = IsLocalRing.ResidueField.map f (IsLocalRing.residue A r) := rfl
    _ = IsLocalRing.ResidueField.map f (ε a) :=
      congrArg (IsLocalRing.ResidueField.map f) hr

omit [IsLocalRing A] [IsLocalHom f] in
private theorem henselian_etale_ringHom_ext
    {B : Type u} [CommRing B] (β : A →+* B) (hβ : β.Etale)
    (g h : B →+* S) (hg : g.comp β = f) (hh : h.comp β = f)
    (hresidue : (IsLocalRing.residue S).comp g = (IsLocalRing.residue S).comp h) :
    g = h := by
  let e : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom β)
  have : Etale e := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hβ
  let p : Spec (.of (IsLocalRing.ResidueField S)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp g))
  have hgSpec : Spec.map (CommRingCat.ofHom g) ≫ e =
      Spec.map (CommRingCat.ofHom f) :=
    (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom g)).symm.trans
      (congrArg (fun k : A →+* S => Spec.map (CommRingCat.ofHom k)) hg)
  have hhSpec : Spec.map (CommRingCat.ofHom h) ≫ e =
      Spec.map (CommRingCat.ofHom f) :=
    (Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom h)).symm.trans
      (congrArg (fun k : A →+* S => Spec.map (CommRingCat.ofHom k)) hh)
  have hgp : Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
      Spec.map (CommRingCat.ofHom g) = p :=
    (Spec.map_comp (CommRingCat.ofHom g)
      (CommRingCat.ofHom (IsLocalRing.residue S))).symm
  have hhp : Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
      Spec.map (CommRingCat.ofHom h) = p :=
    (Spec.map_comp (CommRingCat.ofHom h)
      (CommRingCat.ofHom (IsLocalRing.residue S))).symm.trans
      (congrArg (fun k : B →+* IsLocalRing.ResidueField S =>
        Spec.map (CommRingCat.ofHom k)) hresidue.symm)
  have hp : p ≫ e = Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
      Spec.map (CommRingCat.ofHom f) := by
    rw [← hgp, Category.assoc, hgSpec]
  have heq : Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom h) :=
    (Etale.existsUnique_lift_of_henselianLocalRing S e
      (Spec.map (CommRingCat.ofHom f)) p hp).unique
        ⟨hgSpec, hgp⟩ ⟨hhSpec, hhp⟩
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective heq)

/-- Two local maps out of the actual ordinary henselization agreeing on the
original ring are equal. Affine refinements reduce this to genuine unique
étale lifts over the Henselian target. -/
theorem ordinaryHenselizationLift_unique
    (g : ordinaryHenselization A →+* S) [IsLocalHom g]
    (hg : g.comp (ordinaryHenselizationMap A) = f) :
    g = ordinaryHenselizationLift f := by
  let s : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let h : ordinaryHenselization A →+* S := ordinaryHenselizationLift f
  have hh : h.comp (ordinaryHenselizationMap A) = f :=
    ordinaryHenselizationLift_comp_map f
  have hresidue : (IsLocalRing.residue S).comp g = (IsLocalRing.residue S).comp h :=
    (ordinaryHenselization_localMap_residue f g hg).trans
      (ordinaryHenselization_localMap_residue f h hh).symm
  apply RingHom.ext
  intro a
  obtain ⟨W, t, z, rfl⟩ := geometricStalk_exists_representative s a
  obtain ⟨V, v, j, hV, hj⟩ := geometricStalk_exists_affine_refinement s W t
  have : IsAffine V.left := hV
  let γ : Γ(V.left, ⊤) →+* ordinaryHenselization A := (geometricStalkGerm s V v).hom
  let β : A →+* Γ(V.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ V.hom.appTop).hom
  have hβ : β.Etale := by
    change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of A)).inv).mp
          inferInstance)
    · exact HasRingHomProperty.appTop (P := @Etale)
        (show V.left ⟶ Spec (CommRingCat.of A) from V.hom) inferInstance
  have hγ : γ.comp β = ordinaryHenselizationMap A :=
    geometricStalkGerm_comp_structure (IsLocalRing.residue A) V v
  have hgβ : (g.comp γ).comp β = f := by
    rw [RingHom.comp_assoc, hγ, hg]
  have hhβ : (h.comp γ).comp β = f := by
    rw [RingHom.comp_assoc, hγ, hh]
  have heq : g.comp γ = h.comp γ := henselian_etale_ringHom_ext f β hβ
    (g.comp γ) (h.comp γ) hgβ hhβ
      (congrArg (fun k : ordinaryHenselization A →+* IsLocalRing.ResidueField S =>
        k.comp γ) hresidue)
  have hrep : geometricStalkGerm s V v (j.left.appTop z) =
      geometricStalkGerm s W t z := by
    have hw := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
      j v (etaleSections (Spec (.of A)))
    rw [hj] at hw
    exact ConcreteCategory.congr_hom hw z
  rw [← hrep]
  exact RingHom.congr_fun heq (j.left.appTop z)

/-- The ordinary henselization satisfies its universal property among local
maps to Henselian local rings, with the original base map unchanged. -/
theorem ordinaryHenselization_existsUnique_lift :
    ∃! g : ordinaryHenselization A →+* S,
      IsLocalHom g ∧ g.comp (ordinaryHenselizationMap A) = f := by
  refine ⟨ordinaryHenselizationLift f,
    ⟨inferInstance, ordinaryHenselizationLift_comp_map f⟩, ?_⟩
  intro g hg
  have : IsLocalHom g := hg.1
  exact ordinaryHenselizationLift_unique f g hg.2

end EtaleFundamentalGroups.StrictHenselian
