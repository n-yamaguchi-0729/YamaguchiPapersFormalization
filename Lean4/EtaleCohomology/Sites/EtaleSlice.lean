/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta,
  Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.EtaleRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda

/-!
# Slices of the small étale category

An object of the slice of `X.Etale` over `U` is an étale scheme over `U.left`.
The structural map is étale by the existing cancellation theorem for maps
between schemes étale over the same base. The inverse functor uses composition
with `U.hom`.

The construction adapts `Over.iteratedSliceEquiv` to the small étale category:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/CategoryTheory/Comma/Over/Basic.lean
The small-site functors, explicit proofs and representing-equivalence transport
are the new adaptation. The transported presheaf may take values in any universe.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace EtaleCohomology

variable {X : Scheme.{u}} (U : X.Etale)

/-- Regard a map to `U` in the small étale category as an étale scheme over `U.left`. -/
def etaleSliceForward : Over U ⥤ U.left.Etale where
  obj T := MorphismProperty.Over.mk ⊤ T.hom.left inferInstance
  map f := MorphismProperty.Over.homMk f.left.left
    (congrArg (fun k => k.left) f.w)
  map_id T := by apply MorphismProperty.Over.Hom.ext; rfl
  map_comp f g := by apply MorphismProperty.Over.Hom.ext; rfl

/-- Compose an étale scheme over `U.left` with `U.hom`, retaining its map to `U`. -/
def etaleSliceBackward : U.left.Etale ⥤ Over U where
  obj W := Over.mk (MorphismProperty.Over.homMk W.hom (by rfl) :
    (etalePostcompose U.hom).obj W ⟶ U)
  map f := Over.homMk ((etalePostcompose U.hom).map f)
    (MorphismProperty.Over.Hom.ext f.w)
  map_id W := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

/-- Forgetting the map to `U` from the inverse slice functor is ordinary postcomposition. -/
lemma etaleSliceBackward_forget :
    etaleSliceBackward U ⋙ Over.forget U = etalePostcompose U.hom := rfl

/-- The slice of the small étale category over `U` is the small étale category of `U.left`. -/
def etaleSliceEquiv : Over U ≌ U.left.Etale where
  functor := etaleSliceForward U
  inverse := etaleSliceBackward U
  unitIso := NatIso.ofComponents (fun T =>
    Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change (𝟙 T.left.left) ≫ (T.hom.left ≫ U.hom) = T.left.hom
      exact (Category.id_comp _).trans T.hom.w)) (by
        apply MorphismProperty.Over.Hom.ext
        exact Category.id_comp T.hom.left)) (by
      intro T S f
      apply Over.OverMorphism.ext
      apply MorphismProperty.Over.Hom.ext
      change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
      rw [Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun W =>
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp W.hom)) (by
      intro W V f
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left
      rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp T := by
    apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp (𝟙 T.left.left)

/-- An actual ordinary local representation induces a representation on the
slice of the original small étale category. -/
def representableByEtaleSlice (F : X.Etaleᵒᵖ ⥤ Type v) (W : U.left.Etale)
    (h : ((etalePostcompose U.hom).op ⋙ F).RepresentableBy W) :
    ((Over.forget U).op ⋙ F).RepresentableBy ((etaleSliceEquiv U).inverse.obj W) := by
  let E := etaleSliceEquiv U
  let r : (E.functor.op ⋙ ((etalePostcompose U.hom).op ⋙ F)).RepresentableBy
      (E.inverse.obj W) :=
    { homEquiv := ((E.toAdjunction.homEquiv _ W).symm).trans h.homEquiv
      homEquiv_comp := fun {T S} a b => by
        change h.homEquiv ((E.toAdjunction.homEquiv T W).symm (a ≫ b)) = _
        rw [Adjunction.homEquiv_naturality_left_symm]
        exact h.homEquiv_comp (E.functor.map a) ((E.toAdjunction.homEquiv S W).symm b) }
  let e : E.functor ⋙ etalePostcompose U.hom ≅ Over.forget U := by
    rw [← etaleSliceBackward_forget U]
    exact (Functor.associator E.functor E.inverse (Over.forget U)).symm ≪≫
      Functor.isoWhiskerRight E.unitIso.symm (Over.forget U) ≪≫
        Functor.leftUnitor (Over.forget U)
  exact r.ofIso ((Functor.associator E.functor.op (etalePostcompose U.hom).op F).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op e.symm) F)

end EtaleCohomology
