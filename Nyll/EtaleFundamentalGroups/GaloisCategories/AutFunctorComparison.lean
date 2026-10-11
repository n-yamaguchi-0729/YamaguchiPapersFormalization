/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.Functoriality

/-!
# Coherent maps on automorphism groups

The maps induced by composite functors compose strictly with the composite
comparison. Replacing a functor by a naturally isomorphic one, and using
that isomorphism in the fiber comparison, leaves the induced map unchanged.
-/

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂ z

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C]
variable {D : Type v₁} [Category.{v₂} D]
variable {E : Type w₁} [Category.{w₂} E]

/-- A natural isomorphism between the source functors does not alter the
induced automorphism map when included in the comparison. -/
theorem autHomOfCompIso_isoFunctor
    {H K : C ⥤ D} (α : H ≅ K) {F : D ⥤ FintypeCat.{z}}
    {G : C ⥤ FintypeCat.{z}} (t : K ⋙ F ≅ G) (a : Aut F) :
    autHomOfCompIso H (Functor.isoWhiskerRight α F ≪≫ t) a =
      autHomOfCompIso K t a := by
  apply Aut.ext
  ext X x
  change t.hom.app X (F.map (α.hom.app X)
      (a.hom.app (H.obj X) (F.map (α.inv.app X) (t.inv.app X x)))) =
    t.hom.app X (a.hom.app (K.obj X) (t.inv.app X x))
  apply congrArg (t.hom.app X)
  exact (ConcreteCategory.congr_hom (a.hom.naturality (α.hom.app X))
    (F.map (α.inv.app X) (t.inv.app X x))).symm.trans
      (congrArg (a.hom.app (K.obj X))
        (FintypeCat.inv_hom_id_apply (F.mapIso (α.app X)) (t.inv.app X x)))

/-- Induction on automorphism groups is compatible with composite functors
and their explicit composite fiber comparison. -/
theorem autHomOfCompIso_comp
    (H : C ⥤ D) (K : D ⥤ E)
    {F : E ⥤ FintypeCat.{z}} {G : D ⥤ FintypeCat.{z}}
    {L : C ⥤ FintypeCat.{z}} (tK : K ⋙ F ≅ G) (tH : H ⋙ G ≅ L)
    (a : Aut F) :
    autHomOfCompIso (H ⋙ K)
        (Functor.associator H K F ≪≫ Functor.isoWhiskerLeft H tK ≪≫ tH) a =
      autHomOfCompIso H tH (autHomOfCompIso K tK a) := by
  apply Aut.ext
  ext X x
  rfl

/-- Transfer a pointed endofunctor through a comparison functor and a
specified commuting square of functors. -/
def transportedEndofunctorFiberIso
    (H : C ⥤ D) (K : C ⥤ C) (L : D ⥤ D)
    {F : D ⥤ FintypeCat.{z}} {G : C ⥤ FintypeCat.{z}}
    (e : H ⋙ F ≅ G) (κ : K ⋙ H ≅ H ⋙ L) (t : L ⋙ F ≅ F) :
    K ⋙ G ≅ G :=
  Functor.isoWhiskerLeft K e.symm ≪≫
    (Functor.associator K H F).symm ≪≫
    Functor.isoWhiskerRight κ F ≪≫
    Functor.associator H L F ≪≫
    Functor.isoWhiskerLeft H t ≪≫ e

/-- The transferred endofunctor induces the same automorphism action under
the original comparison of fiber functors. -/
theorem autHomOfCompIso_transportedEndofunctor
    (H : C ⥤ D) (K : C ⥤ C) (L : D ⥤ D)
    {F : D ⥤ FintypeCat.{z}} {G : C ⥤ FintypeCat.{z}}
    (e : H ⋙ F ≅ G) (κ : K ⋙ H ≅ H ⋙ L) (t : L ⋙ F ≅ F)
    (a : Aut F) :
    autHomOfCompIso K (transportedEndofunctorFiberIso H K L e κ t)
        (autHomOfCompIso H e a) =
      autHomOfCompIso H e (autHomOfCompIso L t a) := by
  let q := Functor.associator H L F ≪≫ Functor.isoWhiskerLeft H t ≪≫ e
  have hc :
      Functor.associator K H F ≪≫ Functor.isoWhiskerLeft K e ≪≫
        transportedEndofunctorFiberIso H K L e κ t =
      Functor.isoWhiskerRight κ F ≪≫ q := by
    apply Iso.ext
    ext U z
    change e.hom.app U (t.hom.app (H.obj U)
        (F.map (κ.hom.app U)
          (e.inv.app (K.obj U) (e.hom.app (K.obj U) z)))) =
      e.hom.app U (t.hom.app (H.obj U) (F.map (κ.hom.app U) z))
    exact congrArg
      (fun z => e.hom.app U (t.hom.app (H.obj U) (F.map (κ.hom.app U) z)))
      (FintypeCat.hom_inv_id_apply (e.app (K.obj U)) z)
  calc
    autHomOfCompIso K (transportedEndofunctorFiberIso H K L e κ t)
        (autHomOfCompIso H e a) =
      autHomOfCompIso (K ⋙ H)
        (Functor.associator K H F ≪≫ Functor.isoWhiskerLeft K e ≪≫
          transportedEndofunctorFiberIso H K L e κ t) a :=
      (autHomOfCompIso_comp K H e
        (transportedEndofunctorFiberIso H K L e κ t) a).symm
    _ = autHomOfCompIso (K ⋙ H) (Functor.isoWhiskerRight κ F ≪≫ q) a :=
      congrArg (fun b => autHomOfCompIso (K ⋙ H) b a) hc
    _ = autHomOfCompIso (H ⋙ L) q a := autHomOfCompIso_isoFunctor κ q a
    _ = autHomOfCompIso H e (autHomOfCompIso L t a) :=
      autHomOfCompIso_comp H L t e a

end CategoryTheory.PreGaloisCategory
