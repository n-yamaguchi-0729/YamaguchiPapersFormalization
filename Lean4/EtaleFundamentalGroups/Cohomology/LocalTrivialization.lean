/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.ExtensionFibers
import EtaleCohomology.Constructible.FiniteLocallyConstantSet
import EtaleCohomology.Sites.ConstantPresentation
import EtaleCohomology.Sites.EtaleRestriction
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Types.Basic

/-!
# Étale local trivializations of extension fibers

An actual local lift of the quotient section translates the restricted kernel
onto the extension fiber. Epimorphy supplies a cover with such lifts. In
particular, a finite constant kernel makes the fiber finite locally constant.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

private abbrev toEtaleObject (Y : X.Etale) (V : Y.left.Etale) :
    (etalePostcompose Y.hom).obj V ⟶ Y :=
  MorphismProperty.Over.homMk V.hom rfl

private def restrictedLift (Y : X.Etale)
    (e : {b : S.X₂.obj.obj (op Y) // S.g.hom.app (op Y) b = t.app (op Y) PUnit.unit})
    (V : Y.left.Etaleᵒᵖ) :
    {b : S.X₂.obj.obj ((etalePostcompose Y.hom).op.obj V) //
      S.g.hom.app _ b = t.app _ PUnit.unit} := by
  let k := toEtaleObject Y V.unop
  refine ⟨S.X₂.obj.map k.op e.val, ?_⟩
  have hn := ConcreteCategory.congr_hom (S.g.hom.naturality k.op) e.val
  change S.g.hom.app _ (S.X₂.obj.map k.op e.val) =
    S.X₃.obj.map k.op (S.g.hom.app _ e.val) at hn
  rw [e.property] at hn
  exact hn.trans (ConcreteCategory.congr_hom (t.naturality k.op) PUnit.unit).symm

private lemma restrictedLift_naturality (Y : X.Etale)
    (e : {b : S.X₂.obj.obj (op Y) // S.g.hom.app (op Y) b = t.app (op Y) PUnit.unit})
    {V W : Y.left.Etaleᵒᵖ} (k : V ⟶ W) :
    S.X₂.obj.map ((etalePostcompose Y.hom).op.map k) (restrictedLift S t Y e V).val =
      (restrictedLift S t Y e W).val := by
  change S.X₂.obj.map _ (S.X₂.obj.map _ e.val) = S.X₂.obj.map _ e.val
  rw [← ConcreteCategory.comp_apply, ← S.X₂.obj.map_comp]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  exact k.unop.w

private def translationHom (Y : X.Etale)
    (e : {b : S.X₂.obj.obj (op Y) // S.g.hom.app (op Y) b = t.app (op Y) PUnit.unit}) :
    (etaleRestriction Y.hom (Type u)).obj
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₁) ⟶
      (etaleRestriction Y.hom (Type u)).obj (extensionFiber S t) where
  hom :=
    { app V := ↾fun a =>
        (⟨S.f.hom.app _ a + (restrictedLift S t Y e V).val, by
          change S.g.hom.app _ (S.f.hom.app _ a + (restrictedLift S t Y e V).val) =
            t.app _ PUnit.unit
          rw [map_add]
          have hz := ConcreteCategory.congr_hom
            (congrArg (fun k : S.X₁ ⟶ S.X₃ => k.hom.app
              ((etalePostcompose Y.hom).op.obj V)) S.zero) a
          change S.g.hom.app _ (S.f.hom.app _ a) = 0 at hz
          rw [hz, zero_add]
          exact (restrictedLift S t Y e V).property⟩)
      naturality V W k := by
        apply ConcreteCategory.hom_ext
        intro a
        apply Subtype.ext
        change S.f.hom.app _ (S.X₁.obj.map _ a) + (restrictedLift S t Y e W).val =
          S.X₂.obj.map _ (S.f.hom.app _ a + (restrictedLift S t Y e V).val)
        rw [map_add, restrictedLift_naturality]
        exact congrArg (fun b => b + (restrictedLift S t Y e W).val)
          (ConcreteCategory.congr_hom
            (S.f.hom.naturality ((etalePostcompose Y.hom).op.map k)) a) }

/-- A lift on an étale object identifies the restricted kernel and fiber. -/
def extensionFiberRestrictionIso (hS : S.ShortExact) (Y : X.Etale)
    (e : {b : S.X₂.obj.obj (op Y) // S.g.hom.app (op Y) b = t.app (op Y) PUnit.unit}) :
    (etaleRestriction Y.hom (Type u)).obj
        ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₁) ≅
      (etaleRestriction Y.hom (Type u)).obj (extensionFiber S t) := by
  have hi : ∀ V, IsIso ((translationHom S t Y e).hom.app V) := by
    intro V
    apply (isIso_iff_bijective _).mpr
    exact extensionFiber_translation_bijective S t hS _ (restrictedLift S t Y e V)
  have : IsIso (translationHom S t Y e).hom :=
    (NatTrans.isIso_iff_isIso_app _).mpr hi
  have : IsIso ((sheafToPresheaf Y.left.smallEtaleTopology (Type u)).map
      (translationHom S t Y e)) := (show IsIso (translationHom S t Y e).hom from inferInstance)
  have : IsIso (translationHom S t Y e) :=
    isIso_of_reflects_iso (translationHom S t Y e)
      (sheafToPresheaf Y.left.smallEtaleTopology (Type u))
  exact asIso (translationHom S t Y e)

/-- Epimorphy gives an actual étale cover on which the quotient section lifts. -/
theorem extensionFiber_exists_lift_cover (hS : S.ShortExact) :
    ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
      ∀ a : 𝒰.I₀, ∃ e : S.X₂.obj.obj
        (op (MorphismProperty.Over.mk ⊤ (𝒰.f a) (𝒰.map_prop a))),
        S.g.hom.app _ e = t.app _ PUnit.unit := by
  classical
  let W := etaleBaseObject X
  have hlocal : ∀ x : X, ∃ (Y : X.Etale) (y : Y.left)
      (e : S.X₂.obj.obj (op Y)), Y.hom y = x ∧
        S.g.hom.app (op Y) e = t.app (op Y) PUnit.unit := by
    intro x
    obtain ⟨Y, g, y, hg, hy⟩ := exists_etale_neighborhood_in_sieve
      (Presheaf.imageSieve S.g.hom (t.app (op W) PUnit.unit))
      (extensionFiber_locally_nonempty S t hS (op W)) x
    obtain ⟨e, he⟩ := hg
    refine ⟨Y, y, e, ?_, ?_⟩
    · have hw : g.left ≫ W.hom = Y.hom := g.w
      exact (congrArg (fun k : Y.left ⟶ X => k y) hw).symm.trans hy
    · exact he.trans (ConcreteCategory.congr_hom (t.naturality g.op) PUnit.unit).symm
  choose Y y e hy he using hlocal
  let 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers X (fun x => (Y x).left) (fun x => (Y x).hom)
      (fun x => ⟨x, y x, hy x⟩) (fun x => (Y x).prop)
  exact ⟨𝒰, fun a => ⟨e a, he a⟩⟩

/-- A finite locally constant kernel makes every extension fiber finite locally
constant. The cover and its translation isomorphisms are constructed from exactness. -/
theorem extensionFiber_isFiniteLocallyConstant (hS : S.ShortExact)
    (hF : IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₁)) :
    IsEtaleFiniteLocallyConstantSet (extensionFiber S t) := by
  obtain ⟨𝒰, h𝒰⟩ := extensionFiber_exists_lift_cover S t hS
  apply IsEtaleFiniteLocallyConstantSet.of_cover 𝒰
  intro a
  obtain ⟨e, he⟩ := h𝒰 a
  let Y : X.Etale := MorphismProperty.Over.mk ⊤ (𝒰.f a) (𝒰.map_prop a)
  let E := extensionFiberRestrictionIso S t hS Y ⟨e, he⟩
  let P := etaleSetPullbackRestrictionIso (𝒰.f a)
  exact (hF.pullback (𝒰.f a)).of_iso
    (P.app _ ≪≫ E ≪≫ (P.app _).symm)

/-- Forgetting a constant abelian sheaf gives the same constant sheaf of sets. -/
def constantAbelianUnderlyingIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u}) ≅
      forget AddCommGrpCat.{u} ⋙ constantSheaf X.smallEtaleTopology (Type u) := by
  let : X.smallEtaleTopology.PreservesSheafification (forget AddCommGrpCat.{u}) :=
    GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology (Scheme.AffineEtale.topology X) (Scheme.AffineEtale.Spec X)
      (Type u) (forget AddCommGrpCat.{u})
  exact constantCommuteCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})

/-- Finite constant coefficients satisfy the local-constancy hypothesis without
any geometric condition on the scheme. -/
theorem constantAbelian_isFiniteLocallyConstant (X : Scheme.{u})
    (A : AddCommGrpCat.{u}) [Finite A] :
    IsEtaleFiniteLocallyConstantSet
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)) :=
  (IsEtaleFiniteLocallyConstantSet.constant (X := X) A).of_iso
    ((constantAbelianUnderlyingIso X).app A).symm

end EtaleFundamentalGroups.Cohomology
