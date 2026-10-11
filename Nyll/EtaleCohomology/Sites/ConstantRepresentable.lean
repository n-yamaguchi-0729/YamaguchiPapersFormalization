/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.Subcanonical
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Yoneda

/-!
# Constant étale sheaves represented by disjoint unions

The disjoint union of copies of a scheme indexed by a set represents the
constant sheaf with that set as value. The disjoint open covering gives a
coproduct of represented sheaves, and the constant-sheaf adjunction identifies
that coproduct with the sheafification of the constant presheaf.

The index set need not be finite, and no hypothesis on the base scheme is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v

namespace EtaleCohomology

private def cofanHomEquiv {C : Type*} [Category* C] {ι : Type*}
    {F : ι → C} {c : Cofan F} (hc : IsColimit c) (G : C) :
    (c.pt ⟶ G) ≃ (∀ i, F i ⟶ G) where
  toFun f i := c.inj i ≫ f
  invFun g := hc.desc (Cofan.mk G g)
  left_inv f := by
    apply hc.hom_ext
    intro i
    exact hc.fac (Cofan.mk G (fun j => c.inj j ≫ f)) i
  right_inv g := by
    funext i
    exact hc.fac (Cofan.mk G g) ⟨i⟩

private def coprodConstantHomEquiv {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) [J.Subcanonical] [HasWeakSheafify J (Type u)]
    {T : C} (hT : IsTerminal T) (ι : Type u)
    {D : C} (j : ι → (T ⟶ D))
    (hc : IsColimit (Cofan.mk (J.yoneda.obj D) (fun i => J.yoneda.map (j i))))
    (G : Sheaf J (Type u)) :
    (J.yoneda.obj D ⟶ G) ≃ ((constantSheaf J (Type u)).obj ι ⟶ G) :=
  (cofanHomEquiv hc G).trans
    ((Equiv.piCongrRight (fun _ => J.yonedaEquiv)).trans
      (TypeCat.homEquiv.symm.trans ((constantSheafAdj J (Type u) hT).homEquiv ι G).symm))

private def coprodConstantIso {C : Type v} [Category.{u} C]
    (J : GrothendieckTopology C) [J.Subcanonical] [HasWeakSheafify J (Type u)]
    {T : C} (hT : IsTerminal T) (ι : Type u)
    {D : C} (j : ι → (T ⟶ D))
    (hc : IsColimit (Cofan.mk (J.yoneda.obj D) (fun i => J.yoneda.map (j i)))) :
    J.yoneda.obj D ≅ (constantSheaf J (Type u)).obj ι := by
  let e := coprodConstantHomEquiv J hT ι j hc
  refine (Coyoneda.ext _ _ (fun {G} a => (e G).symm a) (fun {G} a => e G a)
    (fun a => (e _).apply_symm_apply a) (fun a => (e _).symm_apply_apply a) ?_).symm
  intro G H f g
  change ((constantSheafAdj J (Type u) hT).homEquiv ι H).symm
      (↾fun i => J.yonedaEquiv (J.yoneda.map (j i) ≫ (f ≫ g))) =
    ((constantSheafAdj J (Type u) hT).homEquiv ι G).symm
      (↾fun i => J.yonedaEquiv (J.yoneda.map (j i) ≫ f)) ≫ g
  rw [← (constantSheafAdj J (Type u) hT).homEquiv_naturality_right_symm]
  congr 1

/-- The base scheme, viewed as the terminal object of its small étale category. -/
def etaleBaseObject (X : Scheme.{u}) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance

private lemma etale_copies_projection (X : Scheme.{u}) (ι : Type u) :
    Etale (Sigma.desc (fun _ : ι => 𝟙 X)) := by
  let : IsZariskiLocalAtSource (show MorphismProperty Scheme.{u} from @Etale) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)

/-- The disjoint union of copies of the base, as an object of its small étale site. -/
def etaleCopies (X : Scheme.{u}) (ι : Type u) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (Sigma.desc (fun _ : ι => 𝟙 X))
    (etale_copies_projection X ι)

/-- The inclusion of one copy, as a morphism in the small étale category. -/
def etaleCopiesInj (X : Scheme.{u}) (ι : Type u) (i : ι) :
    etaleBaseObject X ⟶ etaleCopies X ι :=
  MorphismProperty.Over.homMk (Sigma.ι (fun _ : ι => X) i) (Sigma.ι_comp_desc _ i)

private def etaleIsInitialOfIsEmpty {X : Scheme.{u}} (Y : X.Etale) [IsEmpty Y.left] :
    IsInitial Y := by
  let hY : IsInitial Y.left := isInitialOfIsEmpty
  let : ∀ Z : X.Etale, Unique (Y ⟶ Z) := fun Z =>
    { default := MorphismProperty.Over.homMk (hY.to Z.left) (hY.hom_ext _ _)
      uniq f := MorphismProperty.Over.Hom.ext (hY.hom_ext _ _) }
  exact IsInitial.ofUnique Y

private lemma empty_cover_of_initial {X : Scheme.{u}} (Y : X.Etale) (hY : IsInitial Y) :
    ⊥ ∈ X.smallEtaleTopology Y := by
  let E : X.Etale := MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) inferInstance
  have : IsEmpty Y.left :=
    ⟨fun y => isEmptyElim (show (∅ : Scheme.{u}) from (hY.to E).left y)⟩
  have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff
    (Z := fun i : PEmpty.{1} => i.elim) (W := Y) (fun i => i.elim)).mpr
      (by ext y; exact isEmptyElim y)
  simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using h

private def etaleCopiesSheafIsColimit (X : Scheme.{u}) (ι : Type u) :
    IsColimit (Cofan.mk (X.smallEtaleTopology.yoneda.obj (etaleCopies X ι))
      (fun i => X.smallEtaleTopology.yoneda.map (etaleCopiesInj X ι i))) := by
  have (i : ι) : Mono ((Cofan.mk (etaleCopies X ι) (etaleCopiesInj X ι)).inj i) := by
    constructor
    intro Y a b hab
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono (Sigma.ι (fun _ : ι => X) i)).mp
      (congrArg (fun f => f.left) hab)
  apply X.smallEtaleTopology.isColimitCofanMkYoneda (fun _ : ι => etaleBaseObject X)
    (c := Cofan.mk (etaleCopies X ι) (etaleCopiesInj X ι))
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover (fun _ : ι => X)).exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  · exact empty_cover_of_initial
  · intro i j hij Y a b hab
    have : IsEmpty Y.left := isEmpty_of_commSq_sigmaι_of_ne
      ⟨congrArg (fun f => f.left) hab⟩ hij
    exact ⟨etaleIsInitialOfIsEmpty Y⟩

/-- A disjoint union of copies of the base represents the constant étale sheaf. -/
def etaleCopiesSheafIso (X : Scheme.{u}) (ι : Type u) :
    X.smallEtaleTopology.yoneda.obj (etaleCopies X ι) ≅
      (constantSheaf X.smallEtaleTopology (Type u)).obj ι :=
  coprodConstantIso X.smallEtaleTopology
    (MorphismProperty.Over.mkIdTerminal (show MorphismProperty Scheme.{u} from @Etale) X)
    ι (etaleCopiesInj X ι) (etaleCopiesSheafIsColimit X ι)

/-- Under the disjoint-union representation, a constant section is the
corresponding component inclusion. -/
lemma etaleCopiesSheafIso_inv_unit (X : Scheme.{u}) (ι : Type u) (i : ι) :
    (etaleCopiesSheafIso X ι).inv.hom.app (op (etaleBaseObject X))
      (((constantSheafAdj X.smallEtaleTopology (Type u)
        (MorphismProperty.Over.mkIdTerminal
          (show MorphismProperty Scheme.{u} from @Etale) X)).unit.app
          ι) i) = etaleCopiesInj X ι i := by
  let hT := MorphismProperty.Over.mkIdTerminal
    (show MorphismProperty Scheme.{u} from @Etale) X
  have he : (constantSheafAdj X.smallEtaleTopology (Type u) hT).homEquiv ι
      (X.smallEtaleTopology.yoneda.obj (etaleCopies X ι))
      (etaleCopiesSheafIso X ι).inv =
    ↾(fun j => X.smallEtaleTopology.yonedaEquiv
      (X.smallEtaleTopology.yoneda.map (etaleCopiesInj X ι j))) := by
    exact (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun f => f i) he

end EtaleCohomology
