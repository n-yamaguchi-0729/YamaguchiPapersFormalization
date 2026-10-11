/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Sites.ConstantPresentation
import EtaleCohomology.Sites.EtaleRestriction
import EtaleCohomology.Sites.ModuleRestriction
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Local lifting of finite free constant sheaves

Finite intersections of image sieves lift a finite free basis along a sheaf
epimorphism. The resulting maps on sections define actual sheaf morphisms
on an étale cover, and the comparison with inverse image is tracked explicitly.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
namespace EtaleCohomology
variable {X : Scheme.{u}} {R : Type u} [CommRing R]

private def sectionRestrictionHom {M : ModuleCat.{u} R}
    (G : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R) (Y : X.Etale) (l : M ⟶ G.obj (op Y)) :
    (Functor.const Y.left.Etaleᵒᵖ).obj M ⟶ (etalePostcompose Y.hom).op ⋙ G where
  app V :=
    let k : (etalePostcompose Y.hom).obj V.unop ⟶ Y :=
      MorphismProperty.Over.homMk V.unop.hom rfl
    l ≫ G.map k.op
  naturality V W k := by
    change 𝟙 M ≫ (l ≫ G.map _) = (l ≫ G.map _) ≫ G.map _
    rw [Category.id_comp, Category.assoc, ← G.map_comp]
    congr 2
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    exact k.unop.w.symm

private lemma sectionRestrictionHom_fac {M : ModuleCat.{u} R}
    {G H : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R}
    (α : (Functor.const X.Etaleᵒᵖ).obj M ⟶ H) (η : G ⟶ H)
    (Y : X.Etale) (l : M ⟶ G.obj (op Y))
    (hl : l ≫ η.app (op Y) = α.app (op Y)) :
    sectionRestrictionHom G Y l ≫ whiskerLeft (etalePostcompose Y.hom).op η =
      whiskerLeft (etalePostcompose Y.hom).op α := by
  apply NatTrans.ext
  funext V
  let k : (etalePostcompose Y.hom).obj V.unop ⟶ Y :=
    MorphismProperty.Over.homMk V.unop.hom rfl
  change (l ≫ G.map k.op) ≫ η.app (op ((etalePostcompose Y.hom).obj V.unop)) =
    α.app (op ((etalePostcompose Y.hom).obj V.unop))
  rw [Category.assoc, η.naturality, ← Category.assoc, hl]
  exact (α.naturality k.op).symm.trans (Category.id_comp _)

/-- Every map from a finite free constant sheaf locally lifts along any
sheaf epimorphism, with the inverse-image comparison in the equality. -/
theorem exists_finiteFreeLift_cover (n : ℕ)
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
      (ModuleCat.of R (Fin n →₀ R)) ⟶ H) (η : G ⟶ H) [Epi η] :
    ∃ 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)),
      ∀ i : 𝒰.I₀, ∃
        (e : (etalePullback (𝒰.f i) R).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj
              (ModuleCat.of R (Fin n →₀ R))) ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)).obj
            (ModuleCat.of R (Fin n →₀ R)))
        (b : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u} R)).obj
            (ModuleCat.of R (Fin n →₀ R)) ⟶ (etalePullback (𝒰.f i) R).obj G),
        b ≫ (etalePullback (𝒰.f i) R).map η = e.inv ≫ (etalePullback (𝒰.f i) R).map α := by
  classical
  have : Sheaf.IsLocallySurjective η := (Sheaf.isLocallySurjective_iff_epi' _ η).mpr inferInstance
  let M : ModuleCat.{u} R := ModuleCat.of R (Fin n →₀ R)
  let α₀ := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ≫ α.hom
  choose Y y l hy hl using fun x : X => exists_constantFreePresentation_lift n α₀ η.hom x
  let 𝒰 : X.Cover.{u} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)) :=
    Scheme.Cover.mkOfCovers X (fun x => (Y x).left) (fun x => (Y x).hom)
      (fun x => ⟨x, y x, hy x⟩) (fun x => (Y x).prop)
  refine ⟨𝒰, fun i => ?_⟩
  let Q := etaleRestriction (Y i).hom (ModuleCat.{u} R)
  let β := sectionRestrictionHom G.obj (Y i) (l i)
  let b₀ : (constantSheaf (Y i).left.smallEtaleTopology (ModuleCat.{u} R)).obj M ⟶ Q.obj G :=
    ⟨sheafifyLift (Y i).left.smallEtaleTopology β (Q.obj G).property⟩
  have hb₀ : b₀ ≫ Q.map η = etaleRestrictionConstantHom (Y i).hom R M ≫ Q.map α := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (Y i).left.smallEtaleTopology _ _ (Q.obj H).property
    change toSheafify (Y i).left.smallEtaleTopology ((Functor.const (Y i).left.Etaleᵒᵖ).obj M) ≫
        sheafifyLift (Y i).left.smallEtaleTopology β (Q.obj G).property ≫
          whiskerLeft (etalePostcompose (Y i).hom).op η.hom =
      toSheafify (Y i).left.smallEtaleTopology ((Functor.const (Y i).left.Etaleᵒᵖ).obj M) ≫
        (etaleRestrictionConstantHom (Y i).hom R M).hom ≫
          whiskerLeft (etalePostcompose (Y i).hom).op α.hom
    erw [← Category.assoc, toSheafify_sheafifyLift, ← Category.assoc,
      etaleRestrictionConstantHom_fac]
    exact sectionRestrictionHom_fac α₀ η.hom (Y i) (l i) (hl i)
  let eP := etalePullbackRestrictionIso (Y i).hom R
  let eR := etaleRestrictionConstantIso (Y i).hom R M
  refine ⟨eP.app _ ≪≫ eR.symm, b₀ ≫ (eP.app G).inv, ?_⟩
  change (b₀ ≫ (eP.app G).inv) ≫ (etalePullback (Y i).hom R).map η =
    (eR.hom ≫ (eP.app _).inv) ≫ (etalePullback (Y i).hom R).map α
  erw [Category.assoc, ← eP.inv.naturality, ← Category.assoc, hb₀,
    Category.assoc, Category.assoc, eP.inv.naturality]
  exact (Category.assoc eR.hom (eP.app _).inv _).symm

end EtaleCohomology
