/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Descent of automorphisms of finite-valued functors

Objects and morphisms descend through a family of stage functors.  A family of
automorphisms compatible with refinement consequently glues to a unique
automorphism.  The descent assumptions concern objects and morphisms in the
underlying categories, not existence or bijectivity of a fundamental-group
comparison map.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

universe u v u' v' w t

private theorem commutes_iso_inv
    {D : Type u} [Category.{v} D] {X Y : D}
    (e : X ≅ Y) (a : X ⟶ X) (b : Y ⟶ Y)
    (h : e.hom ≫ b = a ≫ e.hom) :
    e.inv ≫ a = b ≫ e.inv := by
  apply (cancel_epi e.hom).1
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  rw [h, Category.assoc, e.hom_inv_id, Category.comp_id]

variable {I : Type t} [Preorder I]
variable {C : Type u} [Category.{v} C]
variable (Cstage : I → Type u') [∀ i, Category.{v'} (Cstage i)]
variable (H : ∀ i, Cstage i ⥤ C)
variable (T : ∀ {i j : I}, i ≤ j → Cstage i ⥤ Cstage j)
variable (e : ∀ {i j : I} (hij : i ≤ j), H i ≅ T hij ⋙ H j)
variable (F : C ⥤ FintypeCat.{w})

/-- Eventual descent of morphisms makes a compatible family of stage
automorphisms natural across different stages. -/
theorem stageAut_naturality_of_eventualHom
    (hhom : ∀ (i j : I) (A : Cstage i) (B : Cstage j)
      (f : (H i).obj A ⟶ (H j).obj B),
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
        (g : (T hik).obj A ⟶ (T hjk).obj B),
        f = (e hik).hom.app A ≫ (H k).map g ≫ (e hjk).inv.app B)
    (σ : ∀ i, Aut (H i ⋙ F))
    (hσ : ∀ (i j : I) (hij : i ≤ j) (A : Cstage i),
      F.map ((e hij).hom.app A) ≫ (σ j).hom.app ((T hij).obj A) =
        (σ i).hom.app A ≫ F.map ((e hij).hom.app A))
    (i j : I) (A : Cstage i) (B : Cstage j)
    (f : (H i).obj A ⟶ (H j).obj B) :
    F.map f ≫ (σ j).hom.app B = (σ i).hom.app A ≫ F.map f := by
  obtain ⟨k, hik, hjk, g, rfl⟩ := hhom i j A B f
  have hB :
      F.map ((e hjk).inv.app B) ≫ (σ j).hom.app B =
        (σ k).hom.app ((T hjk).obj B) ≫ F.map ((e hjk).inv.app B) :=
    commutes_iso_inv (F.mapIso ((e hjk).app B))
      ((σ j).hom.app B) ((σ k).hom.app ((T hjk).obj B)) (hσ j k hjk B)
  have hg :
      F.map ((H k).map g) ≫ (σ k).hom.app ((T hjk).obj B) =
        (σ k).hom.app ((T hik).obj A) ≫ F.map ((H k).map g) :=
    (σ k).hom.naturality g
  simp only [F.map_comp, Category.assoc]
  rw [hB, ← Category.assoc (F.map ((H k).map g)), hg,
    Category.assoc, ← Category.assoc (F.map ((e hik).hom.app A)),
    hσ i k hik A]
  exact Category.assoc _ _ _

omit [Preorder I] in
/-- Joint essential surjectivity and naturality on all stage-image morphisms
give a unique global automorphism.  The proof chooses object models and
proves independence through the given morphisms. -/
theorem existsUnique_aut_of_joint_essSurj
    (hobj : ∀ X : C, ∃ (i : I) (A : Cstage i), Nonempty ((H i).obj A ≅ X))
    (σ : ∀ i, Aut (H i ⋙ F))
    (hnat : ∀ (i j : I) (A : Cstage i) (B : Cstage j)
      (f : (H i).obj A ⟶ (H j).obj B),
      F.map f ≫ (σ j).hom.app B = (σ i).hom.app A ≫ F.map f) :
    ∃! a : Aut F, ∀ (i : I) (A : Cstage i),
      a.hom.app ((H i).obj A) = (σ i).hom.app A := by
  classical
  choose idx obj he using hobj
  let iso (X : C) : (H (idx X)).obj (obj X) ≅ X := Classical.choice (he X)
  let component (X : C) : Aut (F.obj X) :=
    (F.mapIso (iso X)).conjAut ((σ (idx X)).app (obj X))
  have hleft (X : C) : F.map (iso X).inv ≫ F.map (iso X).hom = 𝟙 (F.obj X) :=
    (F.mapIso (iso X)).inv_hom_id
  have hright (X : C) : F.map (iso X).hom ≫ F.map (iso X).inv =
      𝟙 (F.obj ((H (idx X)).obj (obj X))) :=
    (F.mapIso (iso X)).hom_inv_id
  have hcomponent (X : C) :
      (component X).hom = F.map (iso X).inv ≫
        (σ (idx X)).hom.app (obj X) ≫ F.map (iso X).hom := by
    exact Iso.conjAut_hom (F.mapIso (iso X)) ((σ (idx X)).app (obj X))
  have hnaturality {X Y : C} (f : X ⟶ Y) :
      F.map f ≫ (component Y).hom = (component X).hom ≫ F.map f := by
    have hn := hnat (idx X) (idx Y) (obj X) (obj Y)
      ((iso X).hom ≫ f ≫ (iso Y).inv)
    have hh := congrArg
      (fun q ↦ F.map (iso X).inv ≫ q ≫ F.map (iso Y).hom) hn
    simp only [F.map_comp, Category.assoc] at hh
    rw [← Category.assoc (F.map (iso X).inv) (F.map (iso X).hom),
      hleft X, Category.id_comp, hleft Y, Category.comp_id] at hh
    simpa only [hcomponent, Category.assoc] using hh
  let a : Aut F := NatIso.ofComponents component (fun f ↦ hnaturality f)
  have ha : ∀ (i : I) (A : Cstage i),
      a.hom.app ((H i).obj A) = (σ i).hom.app A := by
    intro i A
    let X := (H i).obj A
    have hn := hnat (idx X) i (obj X) A (iso X).hom
    have hh := congrArg (fun q ↦ F.map (iso X).inv ≫ q) hn
    change (component X).hom = (σ i).hom.app A
    rw [hcomponent]
    rw [← Category.assoc, hleft X, Category.id_comp] at hh
    exact hh.symm
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply NatTrans.ext
  funext X
  have hn := b.hom.naturality (iso X).hom
  rw [hb (idx X) (obj X)] at hn
  apply (cancel_epi (F.map (iso X).hom)).1
  change F.map (iso X).hom ≫ b.hom.app X =
    F.map (iso X).hom ≫ (component X).hom
  rw [hcomponent, ← Category.assoc (F.map (iso X).hom) (F.map (iso X).inv),
    hright X, Category.id_comp]
  exact hn

/-- Compatible automorphisms descend uniquely once objects and morphisms
descend.  No equality descent or faithfulness of a single stage functor is
required for this automorphism statement. -/
theorem existsUnique_aut_of_eventualHom
    (hobj : ∀ X : C, ∃ (i : I) (A : Cstage i), Nonempty ((H i).obj A ≅ X))
    (hhom : ∀ (i j : I) (A : Cstage i) (B : Cstage j)
      (f : (H i).obj A ⟶ (H j).obj B),
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k)
        (g : (T hik).obj A ⟶ (T hjk).obj B),
        f = (e hik).hom.app A ≫ (H k).map g ≫ (e hjk).inv.app B)
    (σ : ∀ i, Aut (H i ⋙ F))
    (hσ : ∀ (i j : I) (hij : i ≤ j) (A : Cstage i),
      F.map ((e hij).hom.app A) ≫ (σ j).hom.app ((T hij).obj A) =
        (σ i).hom.app A ≫ F.map ((e hij).hom.app A)) :
    ∃! a : Aut F, ∀ (i : I) (A : Cstage i),
      a.hom.app ((H i).obj A) = (σ i).hom.app A := by
  apply existsUnique_aut_of_joint_essSurj Cstage H F hobj σ
  exact stageAut_naturality_of_eventualHom Cstage H T e F hhom σ hσ

end CategoryTheory.PreGaloisCategory
