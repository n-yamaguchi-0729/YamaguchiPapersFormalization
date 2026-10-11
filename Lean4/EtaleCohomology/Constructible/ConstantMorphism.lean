/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ConstantPresentation
import EtaleCohomology.Sites.ConstantRepresentable
import EtaleCohomology.Sites.EtaleRestriction
import EtaleCohomology.Sites.ModuleRestriction
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import EtaleCohomology.Sites.SheafFunctors

/-!
# Local constant models for morphisms of constant module sheaves

A morphism from a finite type constant module sheaf to a constant module
sheaf is, on an actual étale covering, induced by a module homomorphism.
The models and their commutative squares are constructed from finite local
lifts of the sheafification presentation.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

namespace EtaleCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

private lemma restriction_factor {M N : ModuleCat.{u} R}
    {F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R}
    (α : (Functor.const X.Etaleᵒᵖ).obj M ⟶ F)
    (η : (Functor.const X.Etaleᵒᵖ).obj N ⟶ F)
    (Y : X.Etale) (l : M ⟶ N) (hl : α.app (op Y) = l ≫ η.app (op Y)) :
    whiskerLeft (etalePostcompose Y.hom).op α =
      (Functor.const Y.left.Etaleᵒᵖ).map l ≫ whiskerLeft (etalePostcompose Y.hom).op η := by
  apply NatTrans.ext
  funext V
  let k : (etalePostcompose Y.hom).obj V.unop ⟶ Y :=
    MorphismProperty.Over.homMk V.unop.hom rfl
  change α.app (op ((etalePostcompose Y.hom).obj V.unop)) =
    l ≫ η.app (op ((etalePostcompose Y.hom).obj V.unop))
  have hα : α.app (op ((etalePostcompose Y.hom).obj V.unop)) =
      α.app (op Y) ≫ F.map k.op := by
    exact (Category.id_comp _).symm.trans (α.naturality k.op)
  have hη : η.app (op ((etalePostcompose Y.hom).obj V.unop)) =
      η.app (op Y) ≫ F.map k.op := by
    exact (Category.id_comp _).symm.trans (η.naturality k.op)
  rw [hα, hl, Category.assoc, ← hη]

private lemma restriction_constantMorphism_square
    (M N : ModuleCat.{u} R)
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N)
    (Y : X.Etale) (l : M ⟶ N)
    (hl : (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ φ.hom).app
        (op Y) = l ≫
          (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op Y)) :
    etaleRestrictionConstantHom Y.hom R M ≫
        (etaleRestriction Y.hom (ModuleCat.{u} R)).map φ =
      (constantSheaf Y.left.smallEtaleTopology (ModuleCat.{u} R)).map l ≫
        etaleRestrictionConstantHom Y.hom R N := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Y.left.smallEtaleTopology _ _
    ((etaleRestriction Y.hom (ModuleCat.{u} R)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N)).property
  change toSheafify Y.left.smallEtaleTopology ((Functor.const Y.left.Etaleᵒᵖ).obj M) ≫
      (etaleRestrictionConstantHom Y.hom R M).hom ≫
        whiskerLeft (etalePostcompose Y.hom).op φ.hom =
    toSheafify Y.left.smallEtaleTopology ((Functor.const Y.left.Etaleᵒᵖ).obj M) ≫
      sheafifyMap Y.left.smallEtaleTopology ((Functor.const Y.left.Etaleᵒᵖ).map l) ≫
        (etaleRestrictionConstantHom Y.hom R N).hom
  erw [← Category.assoc, etaleRestrictionConstantHom_fac Y.hom R M,
    ← Category.assoc, ← toSheafify_naturality, Category.assoc,
    etaleRestrictionConstantHom_fac Y.hom R N]
  exact restriction_factor
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ φ.hom)
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) Y l hl

/-- A sheaf morphism with finitely generated constant source has actual constant
module models on an étale cover, with the original morphism in the commutative square. -/
theorem exists_constantMorphism_cover
    (M N : ModuleCat.{u} R) [Module.Finite R M]
    (φ : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N) :
    ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
      ∀ i : 𝒰.I₀, ∃ (l : M ⟶ N)
        (eM : (etalePullback (𝒰.f i) R).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M) ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)).obj M)
        (eN : (etalePullback (𝒰.f i) R).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj N) ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)).obj N),
        (etalePullback (𝒰.f i) R).map φ ≫ eN.hom =
          eM.hom ≫ (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)).map l := by
  classical
  choose Y y l hy hl using fun x : X => exists_constantPresentation_factor (X := X) M N
    (F := sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N))
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ φ.hom)
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) x
  let 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers X (fun x => (Y x).left) (fun x => (Y x).hom)
      (fun x => ⟨x, y x, hy x⟩) (fun x => (Y x).prop)
  refine ⟨𝒰, fun i => ?_⟩
  let eP := etalePullbackRestrictionIso (Y i).hom R
  let eM := eP.app _ ≪≫ (etaleRestrictionConstantIso (Y i).hom R M).symm
  let eN := eP.app _ ≪≫ (etaleRestrictionConstantIso (Y i).hom R N).symm
  refine ⟨l i, eM, eN, ?_⟩
  change (etalePullback (Y i).hom R).map φ ≫
      (eP.app _).hom ≫ (etaleRestrictionConstantIso (Y i).hom R N).inv =
    (eP.app _).hom ≫ (etaleRestrictionConstantIso (Y i).hom R M).inv ≫
      (constantSheaf (Y i).left.smallEtaleTopology (ModuleCat.{u} R)).map (l i)
  erw [← Category.assoc, eP.hom.naturality, Category.assoc]
  apply congrArg ((eP.app _).hom ≫ ·)
  apply (cancel_mono (etaleRestrictionConstantIso (Y i).hom R N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [← restriction_constantMorphism_square M N φ (Y i) (l i) (hl i)]
  exact (Iso.inv_hom_id_assoc (etaleRestrictionConstantIso (Y i).hom R M) _).symm

end EtaleCohomology
