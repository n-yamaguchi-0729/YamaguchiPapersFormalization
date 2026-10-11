/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import EtaleFundamentalGroups.FiniteEtale.Connected
import EtaleFundamentalGroups.FiniteEtale.GaloisCategory
import SchemeTheory.FiniteEtale.Basic
import SchemeTheory.FiniteEtale.Geometry
import SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
import SchemeTheory.FiniteEtale.Forget.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import EtaleCohomology.Constructible.Representability
import EtaleCohomology.Constructible.FiniteLocallyConstantSet
import EtaleCohomology.Constructible.FiniteEtaleSheaf
import EtaleCohomology.Sites.BaseChange
import EtaleCohomology.Sites.ConstantRepresentable
import EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Finite étale covers that trivialize finite étale schemes

Over a connected base, the Galois representative of the fiber of a finite
étale scheme supplies a connected finite étale surjective cover. Evaluation
of all morphisms from that representative becomes a coproduct decomposition
after base change. The resulting isomorphism commutes with the projection
to the covering scheme. No connectedness or nonemptiness is required of the
scheme being trivialized.

Finite étale representability then gives a connected finite étale
trivializing cover for every finite locally constant set sheaf.
-/

noncomputable section
universe u v w
open CategoryTheory Limits
namespace CategoryTheory.PreGaloisCategory
variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
  (A W : C) [IsGalois A] (a : F.obj A)
  (ha : Function.Bijective (fun f : A ⟶ W => F.map f a))

include F a ha

private lemma evaluation_surjective_at (b : F.obj A) :
    Function.Surjective (fun f : A ⟶ W => F.map f b) := by
  obtain ⟨σ, hσ⟩ := evaluation_aut_surjective_of_isGalois F A b a
  intro z
  obtain ⟨f, hf⟩ := ha.surjective z
  refine ⟨σ.hom ≫ f, ?_⟩
  simp only [Functor.map_comp, FintypeCat.comp_apply, hσ, hf]

/-- Evaluation on a Galois representative identifies its copies indexed by
morphisms to an object with the product with that object. -/
lemma isIso_evaluation_coproduct_of_galois_representative :
    IsIso (Sigma.desc (fun f : A ⟶ W => prod.lift (𝟙 A) f)) := by
  let G := F ⋙ FintypeCat.incl
  let k := Sigma.desc (fun f : A ⟶ W => prod.lift (𝟙 A) f)
  let c : Cofan (fun _ : A ⟶ W => G.obj A) :=
    Cofan.mk (G.obj (∐ fun _ : A ⟶ W => A))
      (fun f => G.map (Sigma.ι (fun _ : A ⟶ W => A) f))
  have hc : IsColimit c := isColimitCofanMkObjOfIsColimit G _ _ (coproductIsCoproduct _)
  let incl : (Σ _ : A ⟶ W, G.obj A) → G.obj (∐ fun _ : A ⟶ W => A) :=
    fun z => G.map (Sigma.ι (fun _ : A ⟶ W => A) z.1) z.2
  have hσ : Function.Bijective incl :=
    (Cofan.nonempty_isColimit_iff_bijective_fromSigma c).mp ⟨hc⟩
  let e := (PreservesLimitPair.iso G A W) ≪≫ Types.binaryProductIso (G.obj A) (G.obj W)
  have he : Function.Bijective e.hom :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance
  have hfst (z : G.obj (A ⨯ W)) : (e.hom z).1 = G.map prod.fst z := by
    exact ConcreteCategory.congr_hom
      (show e.hom ≫ ↾_root_.Prod.fst = G.map prod.fst by
        simp only [e, Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_fst,
          PreservesLimitPair.iso_hom, prodComparison_fst]) z
  have hsnd (z : G.obj (A ⨯ W)) : (e.hom z).2 = G.map prod.snd z := by
    exact ConcreteCategory.congr_hom
      (show e.hom ≫ ↾_root_.Prod.snd = G.map prod.snd by
        simp only [e, Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_snd,
          PreservesLimitPair.iso_hom, prodComparison_snd]) z
  let ev : (Σ _ : A ⟶ W, G.obj A) → G.obj A × G.obj W :=
    fun z => (z.2, G.map z.1 z.2)
  have hev : Function.Bijective ev := by
    constructor
    · rintro ⟨f, b⟩ ⟨g, c⟩ h
      have hbc : b = c := congrArg _root_.Prod.fst h
      subst c
      have hfg : f = g := evaluation_injective_of_isConnected F A W b
        (congrArg _root_.Prod.snd h)
      subst g
      rfl
    · rintro ⟨b, z⟩
      obtain ⟨f, hf⟩ := evaluation_surjective_at F A W a ha b z
      exact ⟨⟨f, b⟩, _root_.Prod.ext rfl hf⟩
  have hcomp (z : Σ _ : A ⟶ W, G.obj A) :
      e.hom (G.map k (incl z)) = ev z := by
    rcases z with ⟨f, b⟩
    apply _root_.Prod.ext
    · rw [hfst]
      change G.map prod.fst (G.map k (G.map (Sigma.ι _ f) b)) = b
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp only [k, Sigma.ι_comp_desc_assoc, prod.lift_fst, Functor.map_id, types_id_apply]
    · rw [hsnd]
      change G.map prod.snd (G.map k (G.map (Sigma.ι _ f) b)) = G.map f b
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp only [k, Sigma.ι_comp_desc_assoc, prod.lift_snd]
  have hk : Function.Bijective (G.map k) := by
    constructor
    · intro x y hxy
      obtain ⟨s, rfl⟩ := hσ.surjective x
      obtain ⟨t, rfl⟩ := hσ.surjective y
      apply congrArg incl
      apply hev.injective
      rw [← hcomp, ← hcomp, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hev.surjective (e.hom y)
      refine ⟨incl z, he.injective ?_⟩
      exact (hcomp z).trans hz
  have : IsIso (G.map k) := (ConcreteCategory.isIso_iff_bijective _).mpr hk
  exact isIso_of_reflects_iso k G

end CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

/-- Every finite étale scheme over a connected base becomes a finite disjoint
union of copies of the base after a connected finite étale surjective cover. -/
theorem exists_finite_etale_trivialization {X : Scheme.{u}} [ConnectedSpace X]
    (W : FiniteEtale X) :
    ∃ (A : FiniteEtale X) (_ : ConnectedSpace A.left) (_ : Surjective A.hom)
      (ι : Type u) (_ : Finite ι)
      (E : (∐ fun _ : ι => A.left) ≅ Limits.pullback W.hom A.hom),
      E.hom ≫ Limits.pullback.snd W.hom A.hom = Sigma.desc (fun _ : ι => 𝟙 A.left) := by
  let F := CategoryTheory.GaloisCategory.getFiberFunctor (FiniteEtale X)
  obtain ⟨A, a, hA, ha⟩ := exists_galois_representative F W
  let : IsGalois A := hA
  let : ConnectedSpace A.left := connectedSpace_left_of_isConnected A
  have : PreconnectedSpace ↑((Functor.fromPUnit X).obj A.right) :=
    inferInstanceAs (PreconnectedSpace X)
  have : Nonempty ↑((Functor.id Scheme).obj A.left) :=
    inferInstanceAs (Nonempty A.left)
  have hsurj : Surjective A.hom := IsFiniteEtale.surjective A.hom
  let H := forget X
  let HH := H ⋙ Over.forget X
  have : PreservesFiniteCoproducts HH := forgetCompOverForgetPreservesFiniteCoproducts X
  let k : (∐ fun _ : A ⟶ W => A) ⟶ A ⨯ W :=
    Sigma.desc (fun f : A ⟶ W => prod.lift (𝟙 A) f)
  have : IsIso k := isIso_evaluation_coproduct_of_galois_representative F A W a ha
  have hpb : IsPullback (HH.map (prod.fst : A ⨯ W ⟶ A))
      (HH.map (prod.snd : A ⨯ W ⟶ W)) A.hom W.hom :=
    Over.isPullback_of_binaryFan_isLimit _ (isLimitOfHasBinaryProductOfPreservesLimit H A W)
  have : IsIso (sigmaComparison HH (fun _ : A ⟶ W => A)) := by infer_instance
  let E : (∐ fun _ : A ⟶ W => HH.obj A) ≅ Limits.pullback W.hom A.hom :=
    asIso (sigmaComparison HH (fun _ : A ⟶ W => A)) ≪≫
      HH.mapIso (asIso k) ≪≫ hpb.isoPullback ≪≫ pullbackSymmetry A.hom W.hom
  have hp : (hpb.isoPullback ≪≫ pullbackSymmetry A.hom W.hom).hom ≫
      Limits.pullback.snd W.hom A.hom = HH.map (prod.fst : A ⨯ W ⟶ A) :=
    (Category.assoc _ _ _).trans
      ((congrArg (hpb.isoPullback.hom ≫ ·) (pullbackSymmetry_hom_comp_snd A.hom W.hom)).trans
        hpb.isoPullback_hom_fst)
  refine ⟨A, inferInstance, hsurj, A ⟶ W, inferInstance, E, ?_⟩
  apply Sigma.hom_ext
  intro f
  change Sigma.ι (fun _ : A ⟶ W => HH.obj A) f ≫ E.hom ≫
      Limits.pullback.snd W.hom A.hom = _
  change Sigma.ι (fun _ : A ⟶ W => HH.obj A) f ≫
      (sigmaComparison HH (fun _ : A ⟶ W => A) ≫ HH.map k ≫
        (hpb.isoPullback ≪≫ pullbackSymmetry A.hom W.hom).hom) ≫
      Limits.pullback.snd W.hom A.hom = _
  rw [Category.assoc, Category.assoc, hp, ι_comp_sigmaComparison_assoc]
  have hkfst : Sigma.ι (fun _ : A ⟶ W => A) f ≫ k ≫ prod.fst = 𝟙 A := by
    simp only [k, Sigma.ι_comp_desc_assoc, prod.lift_fst]
  exact ((congrArg (HH.map (Sigma.ι (fun _ : A ⟶ W => A) f) ≫ ·)
      (HH.map_comp k prod.fst).symm).trans
        (HH.map_comp (Sigma.ι (fun _ : A ⟶ W => A) f) (k ≫ prod.fst)).symm).trans
    ((congrArg (fun t : A ⟶ A => HH.map t) hkfst).trans
      ((HH.map_id A).trans (Sigma.ι_comp_desc (fun _ : A ⟶ W => 𝟙 A.left) f).symm))

end AlgebraicGeometry.FiniteEtale

namespace EtaleCohomology
open AlgebraicGeometry

/-- A finite locally constant set sheaf on a connected scheme becomes a finite
constant sheaf on a connected finite étale surjective cover. -/
theorem IsEtaleFiniteLocallyConstantSet.exists_finite_etale_trivialization
    {X : Scheme.{u}} [ConnectedSpace X]
    {G : Sheaf X.smallEtaleTopology (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    ∃ A : FiniteEtale X, ConnectedSpace A.left ∧ Surjective A.hom ∧
      ∃ ι : Type u, Finite ι ∧
        Nonempty ((etaleSetPullback A.hom).obj G ≅
          (constantSheaf A.left.smallEtaleTopology (Type u)).obj ι) := by
  obtain ⟨W, ⟨eW⟩⟩ := hG.exists_finiteEtaleSheaf_iso
  obtain ⟨A, hA, hsurj, ι, hι, E, hE⟩ := W.exists_finite_etale_trivialization
  have : Finite ι := hι
  let e : etaleCopies A.left ι ≅
      (etaleBaseChange A.hom).obj ((finiteEtaleToEtale X).obj W) :=
    MorphismProperty.Over.isoMk E hE
  exact ⟨A, hA, hsurj, ι, hι,
    ⟨(etaleSetPullback A.hom).mapIso eW.symm ≪≫
      etaleSetPullbackYonedaObjIso A.hom ((finiteEtaleToEtale X).obj W) ≪≫
      A.left.smallEtaleTopology.yoneda.mapIso e.symm ≪≫ etaleCopiesSheafIso A.left ι⟩⟩

end EtaleCohomology
