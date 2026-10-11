/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Nyll.SchemeTheory.Affine.SpecSectionMap
import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.RingHom.Etale

/-!
# Actual affine étale representatives in the Henselian stalk-map range

An étale algebra map to the strict target gives a pointed affine étale
neighborhood by reduction. Uniqueness of the actual pointed Henselian lift
identifies its section map with that algebra map. Its germ therefore supplies
an actual preimage in the geometric stalk. No comparison or surjectivity is
assumed, and no new colimit is constructed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- The actual affine germ factors the prescribed map once the genuine
pointed lift has been identified. The source-algebra structure and the
construction of the point stay outside this section-ring scope. -/
private theorem geometricStalkToHenselian_affine_factorization
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [HenselianLocalRing S] [IsSepClosed (IsLocalRing.ResidueField S)]
    (f : R →+* S) (e : Spec (.of B) ⟶ Spec (.of R)) [Etale e]
    (t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj (Scheme.Etale.mk e))
    (g : B →+* S)
    (hlift : geometricNeighborhoodHenselianLift f (Scheme.Etale.mk e) t =
      Spec.map (CommRingCat.ofHom g)) :
    ∃ j : CommRingCat.of B ⟶ geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))),
      j ≫ CommRingCat.ofHom (geometricStalkToHenselian f) = CommRingCat.ofHom g := by
  let W : (Spec (.of R)).Etale := Scheme.Etale.mk e
  let γ : Γ(Spec (.of B), ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) W t
  let m : geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (geometricStalkToHenselian f)
  have hγ : γ ≫ m = specLiftSectionMap (Spec.map (CommRingCat.ofHom g)) :=
    (geometricStalkGerm_toSpecLiftSectionMap f W t).trans
      (congrArg (fun k : Spec (.of S) ⟶ Spec (.of B) => specLiftSectionMap k) hlift)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ γ, ?_⟩
  exact (Category.assoc (Scheme.ΓSpecIso (CommRingCat.of B)).inv γ m).trans
    ((congrArg (fun k : Γ(Spec (.of B), ⊤) ⟶ CommRingCat.of S =>
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ k) hγ).trans
        (specLiftSectionMap_affine (CommRingCat.ofHom g)))

/-- A compatible map from an actual étale algebra into the strict target
factors through the actual geometric stalk. Its point and lift equation are
constructed from the original algebra map and its proved base square. -/
theorem geometricStalkToHenselian_factorization_of_etale
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [HenselianLocalRing S] [IsSepClosed (IsLocalRing.ResidueField S)]
    [Algebra R B] [Algebra.Etale R B]
    (f : R →+* S) (g : B →+* S)
    (hbase : g.comp (algebraMap R B) = f) :
    ∃ j : B →+* geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))),
      (geometricStalkToHenselian f).comp j = g := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let W : (Spec (.of R)).Etale :=
    Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  let l : Spec (.of S) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom g)
  have hl : l ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom f) := by
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom g)).symm.trans
        (congrArg (fun k : R →+* S => Spec.map (CommRingCat.ofHom k)) hbase)
  have hpoint :
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ l) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f)) :=
    (Category.assoc (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S))) l
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).trans
      ((congrArg (fun k : Spec (.of S) ⟶ Spec (.of R) =>
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ k) hl).trans
        (Spec.map_comp (CommRingCat.ofHom f)
          (CommRingCat.ofHom (IsLocalRing.residue S))).symm)
  let t : (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W :=
    (show Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) from
      Over.homMk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ l) hpoint)
  have hlift : geometricNeighborhoodHenselianLift f W t = l := by
    apply (Etale.existsUnique_lift_of_henselianLocalRing S W.hom
      (Spec.map (CommRingCat.ofHom f)) t.left
      (t.w.trans (Spec.map_comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (IsLocalRing.residue S))))).unique
    · exact ⟨geometricNeighborhoodHenselianLift_comp f W t,
        geometricNeighborhoodHenselianLift_residue f W t⟩
    · exact ⟨hl, rfl⟩
  obtain ⟨j, hj⟩ := geometricStalkToHenselian_affine_factorization f
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) t g hlift
  exact ⟨j.hom, congrArg CommRingCat.Hom.hom hj⟩

/-- Elementwise preimages are extracted in a ring-only scope, after the
actual affine factorization has been constructed. -/
theorem geometricStalkToHenselian_exists_preimage_of_etale
    {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
    [HenselianLocalRing S] [IsSepClosed (IsLocalRing.ResidueField S)]
    [Algebra R B] [Algebra.Etale R B]
    (f : R →+* S) (g : B →+* S)
    (hbase : g.comp (algebraMap R B) = f) (b : B) :
    ∃ a : geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))),
      geometricStalkToHenselian f a = g b := by
  obtain ⟨j, hj⟩ := geometricStalkToHenselian_factorization_of_etale f g hbase
  exact ⟨j b, RingHom.congr_fun hj b⟩

end EtaleFundamentalGroups.StrictHenselian
