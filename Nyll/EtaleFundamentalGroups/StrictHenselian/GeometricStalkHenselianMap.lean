/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Nyll.SchemeTheory.Affine.SpecSectionMap
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic


/-!
# The actual pointed étale stalk maps to a Henselian target

Every pointed étale neighborhood lifts uniquely to the Henselian target,
including non-affine neighborhoods. Their actual section maps form a cocone,
so the defining presheaf-fiber colimit constructs the ring homomorphism.
Its residue is the original evaluation and it extends the given base map.
No comparison morphism or alternate colimit is assumed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing S]
  (f : R →+* S)

private theorem existsUnique_pointedHenselianLift
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    ∃! l : Spec (.of S) ⟶ W.left,
      l ≫ W.hom = Spec.map (CommRingCat.ofHom f) ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫ l = t.left := by
  apply Etale.existsUnique_lift_of_henselianLocalRing S W.hom
    (Spec.map (CommRingCat.ofHom f)) t.left
  exact t.w.trans (Spec.map_comp (CommRingCat.ofHom f)
    (CommRingCat.ofHom (IsLocalRing.residue S)))

/-- The actual lift of a pointed étale neighborhood into the Henselian target. -/
def geometricNeighborhoodHenselianLift
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    Spec (.of S) ⟶ W.left :=
  (existsUnique_pointedHenselianLift f W t).choose

theorem geometricNeighborhoodHenselianLift_comp
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    geometricNeighborhoodHenselianLift f W t ≫ W.hom =
      Spec.map (CommRingCat.ofHom f) :=
  (existsUnique_pointedHenselianLift f W t).choose_spec.1.1

theorem geometricNeighborhoodHenselianLift_residue
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue S)) ≫
        geometricNeighborhoodHenselianLift f W t = t.left :=
  (existsUnique_pointedHenselianLift f W t).choose_spec.1.2

private theorem geometricNeighborhoodHenselianLift_naturality
    {W V : (Spec (.of R)).Etale} (g : W ⟶ V)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    geometricNeighborhoodHenselianLift f W t ≫ g.left =
      geometricNeighborhoodHenselianLift f V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
          ((IsLocalRing.residue S).comp f)))).fiber.map g t) := by
  apply (existsUnique_pointedHenselianLift f V
    ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.map g t)).unique
  · constructor
    · have hg : g.left ≫ V.hom = W.hom := MorphismProperty.Over.w g
      calc
        (geometricNeighborhoodHenselianLift f W t ≫ g.left) ≫ V.hom =
            geometricNeighborhoodHenselianLift f W t ≫ (g.left ≫ V.hom) :=
          Category.assoc _ _ _
        _ = geometricNeighborhoodHenselianLift f W t ≫ W.hom :=
          congrArg (fun k : W.left ⟶ Spec (.of R) =>
            geometricNeighborhoodHenselianLift f W t ≫ k) hg
        _ = Spec.map (CommRingCat.ofHom f) := geometricNeighborhoodHenselianLift_comp f W t
    · rw [← Category.assoc, geometricNeighborhoodHenselianLift_residue]
      rfl
  · exact ⟨geometricNeighborhoodHenselianLift_comp f V _,
      geometricNeighborhoodHenselianLift_residue f V _⟩

private def henselianNeighborhoodSectionMap
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    Γ(W.left, ⊤) ⟶ CommRingCat.of S :=
  (geometricNeighborhoodHenselianLift f W t).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom

private theorem henselianNeighborhoodSectionMap_naturality
    ⦃W V : (Spec (.of R)).Etale⦄ (g : W ⟶ V)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    g.left.appTop ≫ henselianNeighborhoodSectionMap f W t =
      henselianNeighborhoodSectionMap f V
        ((Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
          ((IsLocalRing.residue S).comp f)))).fiber.map g t) := by
  let l : Spec (.of S) ⟶ W.left := geometricNeighborhoodHenselianLift f W t
  let m : W.left ⟶ V.left := g.left
  let e : Γ(Spec (.of S), ⊤) ⟶ CommRingCat.of S :=
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
  exact (Category.assoc m.appTop l.appTop e).symm.trans
    ((congrArg (fun k : Γ(V.left, ⊤) ⟶ Γ(Spec (.of S), ⊤) => k ≫ e)
      (Scheme.Hom.comp_appTop l m).symm).trans
      (congrArg (fun k : Spec (.of S) ⟶ V.left => k.appTop ≫ e)
        (geometricNeighborhoodHenselianLift_naturality f g t)))

private def geometricStalkToHenselianCat :
    geometricStalk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) ⟶
      CommRingCat.of S :=
  (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
    ((IsLocalRing.residue S).comp f)))).presheafFiberDesc
    (P := etaleSections (Spec (.of R))) (henselianNeighborhoodSectionMap f)
    (fun {W V} g t => henselianNeighborhoodSectionMap_naturality f (W := W) (V := V) g t)

/-- The map out of the actual geometric-stalk colimit into the prescribed
Henselian target, constructed from its genuine pointed lifts. -/
def geometricStalkToHenselian :
    geometricStalk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) →+* S :=
  (geometricStalkToHenselianCat f).hom

/-- The colimit map has the literal section-map value on every germ. -/
theorem geometricStalkGerm_toHenselian
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    geometricStalkGerm (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))) W t ≫
        CommRingCat.ofHom (geometricStalkToHenselian f) =
      (geometricNeighborhoodHenselianLift f W t).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom := by
  have h := (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
    ((IsLocalRing.residue S).comp f)))).toPresheafFiber_presheafFiberDesc
    (P := etaleSections (Spec (.of R))) (henselianNeighborhoodSectionMap f)
    (fun {W V} g t => henselianNeighborhoodSectionMap_naturality f (W := W) (V := V) g t) W t
  exact (congrArg (fun k : geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) ⟶ CommRingCat.of S =>
        geometricStalkGerm (Spec.map (CommRingCat.ofHom
          ((IsLocalRing.residue S).comp f))) W t ≫ k)
      (CommRingCat.ofHom_hom (geometricStalkToHenselianCat f))).trans h

/-- The actual colimit germ equation through the generic section-map API.
The defining naturality proof stays with its original owner. -/
theorem geometricStalkGerm_toSpecLiftSectionMap
    (W : (Spec (.of R)).Etale)
    (t : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f)))).fiber.obj W) :
    geometricStalkGerm (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f))) W t ≫
        CommRingCat.ofHom (geometricStalkToHenselian f) =
      specLiftSectionMap (geometricNeighborhoodHenselianLift f W t) := by
  have h := (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom
    ((IsLocalRing.residue S).comp f)))).toPresheafFiber_presheafFiberDesc
    (P := etaleSections (Spec (.of R))) (henselianNeighborhoodSectionMap f)
    (henselianNeighborhoodSectionMap_naturality f) W t
  exact (congrArg (fun k : geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) ⟶ CommRingCat.of S =>
        geometricStalkGerm (Spec.map (CommRingCat.ofHom
          ((IsLocalRing.residue S).comp f))) W t ≫ k)
      (CommRingCat.ofHom_hom (geometricStalkToHenselianCat f))).trans h

/-- The constructed map extends exactly the prescribed base-ring map. -/
theorem geometricStalkToHenselian_comp_structure :
    (geometricStalkToHenselian f).comp
      (geometricStalkStructureMap ((IsLocalRing.residue S).comp f)) = f := by
  let s : Spec (.of (IsLocalRing.ResidueField S)) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))
  let W : (Spec (.of R)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W := Over.homMk s (Category.comp_id _)
  have hl : geometricNeighborhoodHenselianLift f W t = Spec.map (CommRingCat.ofHom f) := by
    have h := geometricNeighborhoodHenselianLift_comp f W t
    change geometricNeighborhoodHenselianLift f W t ≫ 𝟙 _ = _ at h
    exact (Category.comp_id _).symm.trans h
  let γ : Γ(Spec (.of R), ⊤) ⟶ geometricStalk s := geometricStalkGerm s W t
  let m : geometricStalk s ⟶ CommRingCat.of S := CommRingCat.ofHom (geometricStalkToHenselian f)
  have hγ : γ ≫ m =
      (Spec.map (CommRingCat.ofHom f)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of S)).hom :=
    (geometricStalkGerm_toHenselian f W t).trans
      (congrArg (fun k : Spec (.of S) ⟶ Spec (.of R) =>
        k.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom) hl)
  have hcat : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ γ) ≫ m =
      CommRingCat.ofHom f := by
    rw [Category.assoc, hγ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom hcat

/-- Reduction of the constructed map is exactly the defining evaluation. -/
theorem geometricStalkToHenselian_residue :
    (IsLocalRing.residue S).comp (geometricStalkToHenselian f) =
      (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue S).comp f)))).hom := by
  apply RingHom.ext
  intro a
  obtain ⟨W, t, z, rfl⟩ := geometricStalk_exists_representative
    (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) a
  let γ : Γ(W.left, ⊤) ⟶ geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) :=
    geometricStalkGerm (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) W t
  let m : geometricStalk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) ⟶ CommRingCat.of S :=
    CommRingCat.ofHom (geometricStalkToHenselian f)
  let l : Spec (.of S) ⟶ W.left := geometricNeighborhoodHenselianLift f W t
  let r : CommRingCat.of S ⟶ CommRingCat.of (IsLocalRing.ResidueField S) :=
    CommRingCat.ofHom (IsLocalRing.residue S)
  let eS : Γ(Spec (.of S), ⊤) ⟶ CommRingCat.of S :=
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
  let ek : Γ(Spec (.of (IsLocalRing.ResidueField S)), ⊤) ⟶
      CommRingCat.of (IsLocalRing.ResidueField S) :=
    (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField S))).hom
  let p : Spec (.of (IsLocalRing.ResidueField S)) ⟶ W.left := t.left
  let ε : Γ(W.left, ⊤) ⟶ Γ(Spec (.of (IsLocalRing.ResidueField S)), ⊤) := p.appTop
  have hγ : γ ≫ m = l.appTop ≫ eS := geometricStalkGerm_toHenselian f W t
  have hl : l.appTop ≫ (Spec.map r).appTop = ε :=
    (Scheme.Hom.comp_appTop (Spec.map r) l).symm.trans
      (congrArg (fun k : Spec (.of (IsLocalRing.ResidueField S)) ⟶ W.left => k.appTop)
        (geometricNeighborhoodHenselianLift_residue f W t))
  have h : γ ≫ m ≫ r = ε ≫ ek := by
    calc
      γ ≫ m ≫ r = (γ ≫ m) ≫ r := (Category.assoc _ _ _).symm
      _ = (l.appTop ≫ eS) ≫ r :=
        congrArg (fun k : Γ(W.left, ⊤) ⟶ CommRingCat.of S => k ≫ r) hγ
      _ = l.appTop ≫ (eS ≫ r) := Category.assoc _ _ _
      _ = l.appTop ≫ ((Spec.map r).appTop ≫ ek) :=
        congrArg (fun k : Γ(Spec (.of S), ⊤) ⟶
          CommRingCat.of (IsLocalRing.ResidueField S) => l.appTop ≫ k)
          (Scheme.ΓSpecIso_naturality r).symm
      _ = (l.appTop ≫ (Spec.map r).appTop) ≫ ek := (Category.assoc _ _ _).symm
      _ = ε ≫ ek :=
        congrArg (fun k : Γ(W.left, ⊤) ⟶ Γ(Spec (.of (IsLocalRing.ResidueField S)), ⊤) =>
          k ≫ ek) hl
  have he : γ ≫ geometricStalkEvaluation (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue S).comp f))) = ε ≫ ek :=
    geometricStalkGerm_evaluation
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue S).comp f))) W t
  exact ConcreteCategory.congr_hom (h.trans he.symm) z

/-- The constructed map is local, as its reduction is the actual evaluation. -/
instance geometricStalkToHenselian_isLocalHom :
    IsLocalHom (geometricStalkToHenselian f) := by
  have : IsLocalHom ((IsLocalRing.residue S).comp (geometricStalkToHenselian f)) := by
    rw [geometricStalkToHenselian_residue]
    infer_instance
  exact isLocalHom_of_comp (geometricStalkToHenselian f) (IsLocalRing.residue S)

end EtaleFundamentalGroups.StrictHenselian
