/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.PullbackGlobalSectionsComposition
import Nyll.EtaleCohomology.Sites.PullbackUnitGeometricStalks
import Nyll.EtaleCohomology.Sites.PushforwardStalkComposition

/-!
# Composition of the concrete inverse-image stalk maps

The actual adjunction units and direct-image component maps commute with
composition of scheme morphisms. This identifies the two successive maps
on stalks through the chosen inverse-image composition isomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Y Z : Scheme.{u}} (p : Z ⟶ Y) (q : Y ⟶ X)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ X)
  (s : {s : Spec (CommRingCat.of Ω) ⟶ Y // s ≫ q = t})
  (r : {r : Spec (CommRingCat.of Ω) ⟶ Z // r ≫ p = s.val})
  (Λ : Type u) [CommRing Λ]

/-- The concrete inverse-image stalk maps compose under the canonical
comparison between a composite inverse image and an iterated inverse image. -/
theorem etalePullbackUnit_stalkComponent_comp
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Scheme.pointSmallEtale t).sheafFiber.map
        ((etalePullbackPushforwardAdjunction (p ≫ q) Λ).unit.app F) ≫
      etalePushforwardStalkComponent (p ≫ q) t
        ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩
        ((etalePullback (p ≫ q) Λ).obj F)) ≫
      (Scheme.pointSmallEtale r.val).sheafFiber.map
        ((etalePullbackCompIso p q Λ).hom.app F) =
      ((Scheme.pointSmallEtale t).sheafFiber.map
          ((etalePullbackPushforwardAdjunction q Λ).unit.app F) ≫
        etalePushforwardStalkComponent q t s ((etalePullback q Λ).obj F)) ≫
      ((Scheme.pointSmallEtale s.val).sheafFiber.map
          ((etalePullbackPushforwardAdjunction p Λ).unit.app ((etalePullback q Λ).obj F)) ≫
        etalePushforwardStalkComponent p s.val r
          ((etalePullback p Λ).obj ((etalePullback q Λ).obj F))) := by
  let Fq : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback q Λ).obj F
  let Fc : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback (p ≫ q) Λ).obj F
  let Fpq : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePullback p Λ).obj Fq
  let ηq : F ⟶ (etalePushforward q Λ).obj Fq :=
    (etalePullbackPushforwardAdjunction q Λ).unit.app F
  let ηp : Fq ⟶ (etalePushforward p Λ).obj Fpq :=
    (etalePullbackPushforwardAdjunction p Λ).unit.app Fq
  let ηc : F ⟶ (etalePushforward (p ≫ q) Λ).obj Fc :=
    (etalePullbackPushforwardAdjunction (p ≫ q) Λ).unit.app F
  let e : Fc ⟶ Fpq := (etalePullbackCompIso p q Λ).hom.app F
  let h : (etalePushforward q Λ).obj ((etalePushforward p Λ).obj Fpq) ⟶
      (etalePushforward (p ≫ q) Λ).obj Fpq :=
    (etalePushforwardCompIso p q Λ).hom.app Fpq
  let rc : {a : Spec (CommRingCat.of Ω) ⟶ Z // a ≫ (p ≫ q) = t} :=
    ⟨r.val, by rw [← Category.assoc, r.property, s.property]⟩
  let T := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u} Λ)
  let S := (Scheme.pointSmallEtale s.val).sheafFiber (A := ModuleCat.{u} Λ)
  let R := (Scheme.pointSmallEtale r.val).sheafFiber (A := ModuleCat.{u} Λ)
  let cq : T.obj ((etalePushforward q Λ).obj Fq) ⟶ S.obj Fq :=
    etalePushforwardStalkComponent q t s Fq
  let cq' : T.obj ((etalePushforward q Λ).obj ((etalePushforward p Λ).obj Fpq)) ⟶
      S.obj ((etalePushforward p Λ).obj Fpq) :=
    etalePushforwardStalkComponent q t s ((etalePushforward p Λ).obj Fpq)
  let cp : S.obj ((etalePushforward p Λ).obj Fpq) ⟶ R.obj Fpq :=
    etalePushforwardStalkComponent p s.val r Fpq
  let cc : T.obj ((etalePushforward (p ≫ q) Λ).obj Fc) ⟶ R.obj Fc :=
    etalePushforwardStalkComponent (p ≫ q) t rc Fc
  let cc' : T.obj ((etalePushforward (p ≫ q) Λ).obj Fpq) ⟶ R.obj Fpq :=
    etalePushforwardStalkComponent (p ≫ q) t rc Fpq
  have hc : T.map ((etalePushforward (p ≫ q) Λ).map e) ≫ cc' = cc ≫ R.map e :=
    etalePushforwardStalkComponent_naturality (p ≫ q) t rc e
  have hq : T.map ((etalePushforward q Λ).map ηp) ≫ cq' = cq ≫ S.map ηp :=
    etalePushforwardStalkComponent_naturality q t s ηp
  have hcomp : T.map h ≫ cc' = cq' ≫ cp :=
    etalePushforwardStalkComponent_comp p q t s r Λ Fpq
  have hu : T.map ηc ≫ T.map ((etalePushforward (p ≫ q) Λ).map e) =
      (T.map ηq ≫ T.map ((etalePushforward q Λ).map ηp)) ≫ T.map h := by
    rw [← T.map_comp, ← T.map_comp, ← T.map_comp]
    exact congrArg T.map (etalePullbackComp_unit p q Λ F)
  change (T.map ηc ≫ cc) ≫ R.map e = (T.map ηq ≫ cq) ≫ (S.map ηp ≫ cp)
  calc
    (T.map ηc ≫ cc) ≫ R.map e =
        (T.map ηc ≫ T.map ((etalePushforward (p ≫ q) Λ).map e)) ≫ cc' := by
      rw [Category.assoc, ← hc, ← Category.assoc]
    _ = ((T.map ηq ≫ T.map ((etalePushforward q Λ).map ηp)) ≫ T.map h) ≫ cc' :=
      congrArg (fun k => k ≫ cc') hu
    _ = T.map ηq ≫ ((T.map ((etalePushforward q Λ).map ηp) ≫ cq') ≫ cp) := by
      rw [Category.assoc, hcomp]
      simp only [Category.assoc]
    _ = (T.map ηq ≫ cq) ≫ (S.map ηp ≫ cp) := by
      rw [hq]
      simp only [Category.assoc]

end EtaleCohomology
