/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Actual sections pulled through a local factor

A commuting scheme square supplies an actual morphism into the small-site
base change. Restricting the existing adjunction unit along this morphism
pulls sections to the source. Naturality retains equations of local lifts
against a global section, including along a finite refinement.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X)

/-- The actual small-site arrow supplied by a commuting scheme square. -/
def etaleBaseChangeLift {U : Y.Etale} {V : X.Etale}
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q) :
    U ⟶ (etaleBaseChange q).obj V :=
  MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    (pullback.lift l U.hom hl) (pullback.lift_snd l U.hom hl)

variable (Λ : Type u) [CommRing Λ]

/-- Pull a section through an actual local factor, using the chosen unit. -/
def etalePullbackSectionMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V : X.Etale} (l : U.left ⟶ V.left)
    (hl : l ≫ V.hom = U.hom ≫ q) :
    F.obj.obj (op V) ⟶ ((etalePullback q Λ).obj F).obj.obj (op U) :=
  ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op V) ≫
    ((etalePullback q Λ).obj F).obj.map (etaleBaseChangeLift q l hl).op

/-- The actual map on global sections induced by inverse image. -/
def etalePullbackGlobalSectionsMap (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  etalePullbackSectionMap q Λ F q ((Category.comp_id q).trans (Category.id_comp q).symm)

/-- Pulling a local section commutes with an actual sheaf morphism. -/
lemma etalePullbackSectionMap_naturality
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)} (η : F ⟶ G)
    {U : Y.Etale} {V : X.Etale} (l : U.left ⟶ V.left)
    (hl : l ≫ V.hom = U.hom ≫ q) :
    etalePullbackSectionMap q Λ F l hl ≫ ((etalePullback q Λ).map η).hom.app (op U) =
      η.hom.app (op V) ≫ etalePullbackSectionMap q Λ G l hl := by
  let W : Y.Etale := (etaleBaseChange q).obj V
  let a : U ⟶ W := etaleBaseChangeLift q l hl
  let PF : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := ((etalePullback q Λ).obj F).obj
  let PG : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := ((etalePullback q Λ).obj G).obj
  let ηq : PF ⟶ PG := ((etalePullback q Λ).map η).hom
  let uF : F.obj.obj (op V) ⟶ PF.obj (op W) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app F).hom.app (op V)
  let uG : G.obj.obj (op V) ⟶ PG.obj (op W) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app G).hom.app (op V)
  let rF : PF.obj (op W) ⟶ PF.obj (op U) := PF.map a.op
  let rG : PG.obj (op W) ⟶ PG.obj (op U) := PG.map a.op
  let ηV : F.obj.obj (op V) ⟶ G.obj.obj (op V) := η.hom.app (op V)
  let ηW : PF.obj (op W) ⟶ PG.obj (op W) := ηq.app (op W)
  let ηU : PF.obj (op U) ⟶ PG.obj (op U) := ηq.app (op U)
  have hu : ηV ≫ uG = uF ≫ ηW :=
    congrArg (fun k : F ⟶ (etalePushforward q Λ).obj
      ((etalePullback q Λ).obj G) => k.hom.app (op V))
      ((etalePullbackPushforwardAdjunction q Λ).unit.naturality η)
  have hη : rF ≫ ηU = ηW ≫ rG := ηq.naturality a.op
  change (uF ≫ rF) ≫ ηU = ηV ≫ (uG ≫ rG)
  rw [Category.assoc, hη, ← Category.assoc, ← hu, Category.assoc]

private lemma etaleBaseChange_identity_hom_eq {U : Y.Etale}
    (a b : U ⟶ (etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X))) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 X) q)).mp
  exact a.w.trans b.w.symm

/-- A local pullback of the restriction of a global section is the
restriction of its actual global pullback. -/
lemma etalePullbackSectionMap_global_restriction
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    {U : Y.Etale} {V : X.Etale} (g : V ⟶ Scheme.Etale.mk (𝟙 X))
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q) :
    G.obj.map g.op ≫ etalePullbackSectionMap q Λ G l hl =
      etalePullbackGlobalSectionsMap q Λ G ≫ ((etalePullback q Λ).obj G).obj.map
        (MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (A := U) (B := Scheme.Etale.mk (𝟙 Y)) U.hom (Category.comp_id U.hom)).op := by
  let H : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ := ((etalePullback q Λ).obj G).obj
  let V₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  let U₀ : Y.Etale := Scheme.Etale.mk (𝟙 Y)
  let W : Y.Etale := (etaleBaseChange q).obj V
  let W₀ : Y.Etale := (etaleBaseChange q).obj V₀
  let a : U ⟶ W := etaleBaseChangeLift q l hl
  let b : U₀ ⟶ W₀ :=
    etaleBaseChangeLift q q ((Category.comp_id q).trans (Category.id_comp q).symm)
  let j : U ⟶ U₀ := MorphismProperty.Over.homMk
    (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
    U.hom (Category.comp_id U.hom)
  let gq : W ⟶ W₀ := (etaleBaseChange q).map g
  have hab : a ≫ gq = j ≫ b := etaleBaseChange_identity_hom_eq q _ _
  let uV : G.obj.obj (op V) ⟶ H.obj (op W) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app G).hom.app (op V)
  let u₀ : G.obj.obj (op V₀) ⟶ H.obj (op W₀) :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app G).hom.app (op V₀)
  let r : G.obj.obj (op V₀) ⟶ G.obj.obj (op V) := G.obj.map g.op
  let ha : H.obj (op W) ⟶ H.obj (op U) := H.map a.op
  let hb : H.obj (op W₀) ⟶ H.obj (op U₀) := H.map b.op
  let hj : H.obj (op U₀) ⟶ H.obj (op U) := H.map j.op
  let hg : H.obj (op W₀) ⟶ H.obj (op W) := H.map gq.op
  have hunit : r ≫ uV = u₀ ≫ hg :=
    ((etalePullbackPushforwardAdjunction q Λ).unit.app G).hom.naturality g.op
  have hmap : hg ≫ ha = hb ≫ hj := by
    calc
      hg ≫ ha = H.map (a ≫ gq).op := (H.map_comp gq.op a.op).symm
      _ = H.map (j ≫ b).op := congrArg (fun k : U ⟶ W₀ => H.map k.op) hab
      _ = hb ≫ hj := H.map_comp b.op j.op
  change r ≫ (uV ≫ ha) = (u₀ ≫ hb) ≫ hj
  rw [← Category.assoc, hunit, Category.assoc, hmap, ← Category.assoc]

/-- An actual local lift remains a lift after pullback through its local
factor, with the original global section transported by the actual unit. -/
theorem etalePullbackSectionMap_local_lift
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)} (η : F ⟶ G)
    {U : Y.Etale} {V : X.Etale} (g : V ⟶ Scheme.Etale.mk (𝟙 X))
    (l : U.left ⟶ V.left) (hl : l ≫ V.hom = U.hom ≫ q)
    (a : F.obj.obj (op V)) (t : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (ha : η.hom.app (op V) a = G.obj.map g.op t) :
    ((etalePullback q Λ).map η).hom.app (op U) (etalePullbackSectionMap q Λ F l hl a) =
      ((etalePullback q Λ).obj G).obj.map
        (MorphismProperty.Over.homMk
          (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
          (A := U) (B := Scheme.Etale.mk (𝟙 Y)) U.hom (Category.comp_id U.hom)).op
        (etalePullbackGlobalSectionsMap q Λ G t) := by
  have hn := congrArg (fun k : F.obj.obj (op V) ⟶
      ((etalePullback q Λ).obj G).obj.obj (op U) => k a)
    (etalePullbackSectionMap_naturality q Λ η l hl)
  have hg := congrArg (fun k : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((etalePullback q Λ).obj G).obj.obj (op U) => k t)
    (etalePullbackSectionMap_global_restriction q Λ G g l hl)
  change ((etalePullback q Λ).map η).hom.app (op U)
      (etalePullbackSectionMap q Λ F l hl a) =
    etalePullbackSectionMap q Λ G l hl (η.hom.app (op V) a) at hn
  rw [ha] at hn
  exact hn.trans hg

end EtaleCohomology
