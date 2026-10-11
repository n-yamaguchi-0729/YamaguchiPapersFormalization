/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Free abelian representables and actual sheaf sections

The free abelian sheaves used in mathlib's `Sheaf.cohomologyPresheaf`
corepresent evaluation. We record this equivalence and its two naturalities
so that local lifting of sections can be applied to the actual Ext groups.
-/

noncomputable section
universe v u
open CategoryTheory Opposite

namespace EtaleCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- The same free abelian representable functor used by actual sheaf cohomology. -/
abbrev freeAbelianSheafYoneda : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _

/-- Sheafification, the free abelian adjunction, and Yoneda identify morphisms
from a free abelian representable with actual sections. -/
def freeAbelianSheafYonedaHomEquiv (V : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeAbelianSheafYoneda J).obj V ⟶ F) ≃ F.obj.obj (op V) :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
    (yoneda.obj V ⋙ AddCommGrpCat.free) F).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) F.obj).trans yonedaEquiv)

/-- The equivalence evaluates the sheafified morphism on the identity generator. -/
theorem freeAbelianSheafYonedaHomEquiv_apply (V : C)
    (F : Sheaf J AddCommGrpCat.{v}) (a : (freeAbelianSheafYoneda J).obj V ⟶ F) :
    freeAbelianSheafYonedaHomEquiv J V F a =
      (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
        (yoneda.obj V ⋙ AddCommGrpCat.free) F a).app (op V))
          (FreeAbelianGroup.of (𝟙 V)) := rfl

/-- Evaluation is natural in the coefficient sheaf. -/
theorem freeAbelianSheafYonedaHomEquiv_postcomp (V : C)
    {F G : Sheaf J AddCommGrpCat.{v}}
    (a : (freeAbelianSheafYoneda J).obj V ⟶ F) (η : F ⟶ G) :
    freeAbelianSheafYonedaHomEquiv J V G (a ≫ η) =
      η.hom.app (op V) (freeAbelianSheafYonedaHomEquiv J V F a) := by
  rw [freeAbelianSheafYonedaHomEquiv_apply, Adjunction.homEquiv_naturality_right]
  rfl

/-- Evaluation is natural in the object of the site. -/
theorem freeAbelianSheafYonedaHomEquiv_precomp {V W : C} (f : V ⟶ W)
    (F : Sheaf J AddCommGrpCat.{v}) (a : (freeAbelianSheafYoneda J).obj W ⟶ F) :
    freeAbelianSheafYonedaHomEquiv J V F ((freeAbelianSheafYoneda J).map f ≫ a) =
      F.obj.map f.op (freeAbelianSheafYonedaHomEquiv J W F a) := by
  let b : yoneda.obj W ⋙ AddCommGrpCat.free ⟶ F.obj :=
    (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
      (yoneda.obj W ⋙ AddCommGrpCat.free) F a
  rw [freeAbelianSheafYonedaHomEquiv_apply]
  change (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F
    ((presheafToSheaf J AddCommGrpCat.{v}).map
      (Functor.whiskerRight (yoneda.map f) AddCommGrpCat.free) ≫ a)).app (op V))
        (FreeAbelianGroup.of (𝟙 V)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change b.app (op V) (FreeAbelianGroup.of ((𝟙 V) ≫ f)) =
    F.obj.map f.op (b.app (op W) (FreeAbelianGroup.of (𝟙 W)))
  rw [Category.id_comp]
  have h := ConcreteCategory.congr_hom (b.naturality f.op)
    (FreeAbelianGroup.of (𝟙 W))
  change b.app (op V) (FreeAbelianGroup.of (f ≫ 𝟙 W)) =
    F.obj.map f.op (b.app (op W) (FreeAbelianGroup.of (𝟙 W))) at h
  simpa only [Category.comp_id] using h

/-- At a terminal object, the free abelian representable is the actual
constant integer sheaf. Both objects corepresent the same evaluation functor. -/
def freeAbelianSheafYonedaTerminalIso {T : C} (hT : Limits.IsTerminal T) :
    (freeAbelianSheafYoneda J).obj T ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) := by
  let E : Sheaf J AddCommGrpCat.{v} ⥤ Type v :=
    sheafToPresheaf J AddCommGrpCat.{v} ⋙
      (evaluation _ _).obj (op T) ⋙ forget AddCommGrpCat.{v}
  let e : E.CorepresentableBy ((freeAbelianSheafYoneda J).obj T) :=
    { homEquiv := freeAbelianSheafYonedaHomEquiv J T _
      homEquiv_comp := fun η a => freeAbelianSheafYonedaHomEquiv_postcomp J T a η }
  let e' : E.CorepresentableBy
      ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))) :=
    { homEquiv := fun {F} =>
        ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ F).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv
      homEquiv_comp := by
        intro F G η a
        change AddCommGrpCat.uliftZMultiplesAddEquiv _
          ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ G (a ≫ η)) = _
        rw [Adjunction.homEquiv_naturality_right]
        rfl }
  exact e.uniqueUpToIso e'

/-- The actual cohomology presheaf at a terminal object agrees with actual
classical sheaf cohomology in every degree. -/
def sheafCohomologyTerminalEquiv
    [CategoryTheory.HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {T : C} (hT : Limits.IsTerminal T) (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) :
    Sheaf.H.{v} F n ≃+ Sheaf.H'.{v} F n T :=
  (((CategoryTheory.Abelian.extFunctor n).mapIso
    (freeAbelianSheafYonedaTerminalIso J hT).op).app F).addCommGroupIsoToAddEquiv


/-- A singleton cover gives the first coequalizer of the actual free
abelian Cech resolution. The relation maps are the two actual pullback
projections, not a supplied descent comparison. -/
abbrev freeAbelianSheafYonedaCoverCofork {V W : C} (f : V ⟶ W)
    [Limits.HasPullback f f] :
    Limits.Cofork
      ((freeAbelianSheafYoneda J).map (Limits.pullback.fst f f))
      ((freeAbelianSheafYoneda J).map (Limits.pullback.snd f f)) :=
  Limits.Cofork.ofπ ((freeAbelianSheafYoneda J).map f) (by
    rw [← Functor.map_comp, ← Functor.map_comp, Limits.pullback.condition])

/-- Sheaf descent proves the coequalizer universal property for a covering
morphism. This is the degree-zero exactness input for the actual Cech
resolution used in field/Galois cohomology comparison. -/
def freeAbelianSheafYonedaCoverIsColimit {V W : C} (f : V ⟶ W)
    [Limits.HasPullback f f] (hf : Sieve.generate (Presieve.singleton f) ∈ J W) :
    Limits.IsColimit (freeAbelianSheafYonedaCoverCofork J f) := by
  apply Limits.Cofork.IsColimit.ofExistsUnique
  intro s
  let F : Sheaf J AddCommGrpCat.{v} := s.pt
  let a : (freeAbelianSheafYoneda J).obj V ⟶ F := s.π
  have hF : Presieve.IsSheafFor (F.obj ⋙ forget AddCommGrpCat.{v})
      (Presieve.singleton f) :=
    (Presieve.isSheafFor_iff_generate _).mpr
      ((isSheaf_iff_isSheaf_of_type J _).mp
        (Presheaf.isSheaf_comp_of_isSheaf J F.obj
          (forget AddCommGrpCat.{v}) F.property) _ hf)
  have ha : ∀ {Z : C} (p q : Z ⟶ V), p ≫ f = q ≫ f →
      (freeAbelianSheafYoneda J).map p ≫ a =
        (freeAbelianSheafYoneda J).map q ≫ a := by
    intro Z p q hpq
    let l : Z ⟶ Limits.pullback f f := Limits.pullback.lift p q hpq
    calc
      (freeAbelianSheafYoneda J).map p ≫ a =
          (freeAbelianSheafYoneda J).map l ≫
            (freeAbelianSheafYoneda J).map (Limits.pullback.fst f f) ≫ a := by
              rw [← Category.assoc, ← Functor.map_comp, Limits.pullback.lift_fst]
      _ = (freeAbelianSheafYoneda J).map l ≫
            (freeAbelianSheafYoneda J).map (Limits.pullback.snd f f) ≫ a := by
              rw [s.condition]
      _ = (freeAbelianSheafYoneda J).map q ≫ a := by
              rw [← Category.assoc, ← Functor.map_comp, Limits.pullback.lift_snd]
  obtain ⟨t, ht, huniq⟩ := (Presieve.isSheafFor_singleton.mp hF)
    (freeAbelianSheafYonedaHomEquiv J V F a) (by
      intro Z p q hpq
      change F.obj.map p.op _ = F.obj.map q.op _
      rw [← freeAbelianSheafYonedaHomEquiv_precomp,
        ← freeAbelianSheafYonedaHomEquiv_precomp, ha p q hpq])
  let d : (freeAbelianSheafYoneda J).obj W ⟶ F :=
    (freeAbelianSheafYonedaHomEquiv J W F).symm t
  refine ⟨d, ?_, ?_⟩
  · apply (freeAbelianSheafYonedaHomEquiv J V F).injective
    change freeAbelianSheafYonedaHomEquiv J V F
      ((freeAbelianSheafYoneda J).map f ≫ d) = _
    rw [freeAbelianSheafYonedaHomEquiv_precomp]
    exact (congrArg (F.obj.map f.op)
      ((freeAbelianSheafYonedaHomEquiv J W F).apply_symm_apply t)).trans ht
  · intro d' hd'
    apply (freeAbelianSheafYonedaHomEquiv J W F).injective
    change _ = freeAbelianSheafYonedaHomEquiv J W F
      ((freeAbelianSheafYonedaHomEquiv J W F).symm t)
    rw [Equiv.apply_symm_apply]
    apply huniq
    change F.obj.map f.op (freeAbelianSheafYonedaHomEquiv J W F d') = _
    rw [← freeAbelianSheafYonedaHomEquiv_precomp]
    exact congrArg (freeAbelianSheafYonedaHomEquiv J V F) hd'

/-- The augmentation of the free abelian Cech resolution of a singleton
cover is an epimorphism of actual abelian sheaves. -/
theorem freeAbelianSheafYoneda_map_epi_of_cover {V W : C} (f : V ⟶ W)
    [Limits.HasPullback f f] (hf : Sieve.generate (Presieve.singleton f) ∈ J W) :
    Epi ((freeAbelianSheafYoneda J).map f) :=
  Limits.epi_of_isColimit_cofork (freeAbelianSheafYonedaCoverIsColimit J f hf)

end EtaleCohomology
