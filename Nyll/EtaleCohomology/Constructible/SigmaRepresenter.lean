/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Nyll.EtaleCohomology.Sites.Subcanonical
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.SigmaPullback
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Logic.Function.Basic

/-!
# Representers over a disjoint union

An étale covering of the base detects isomorphisms of set-valued sheaves
by bijectivity on the member sites. Pulling the cover back to each test
scheme gives the local lifting and local equality conditions. This applies
in particular to the disjoint open cover of a coproduct, without a
finiteness hypothesis on its index set.

The disjoint union of a small family of étale objects gives a coproduct of
represented sheaves. The local universal sections therefore glue to a section
on the disjoint union of the representers. Cartesian squares for the component
inclusions identify its local Yoneda maps with the given representing
equivalences, proving actual representability on the union of the bases.

Finite étale local models give a finite étale representer, since finiteness
of a morphism is local on its target. The index set need not be finite.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u v

namespace EtaleCohomology

variable {X : Scheme.{u}}
  (𝒰 : X.Cover.{v} (Scheme.precoverage (show MorphismProperty Scheme.{u} from @Etale)))

private def coverRestrictionObject (T : X.Etale) (i : 𝒰.I₀) : X.Etale :=
  (etalePostcompose (𝒰.f i)).obj ((etaleBaseChange (𝒰.f i)).obj T)

private def coverRestrictionMap (T : X.Etale) (i : 𝒰.I₀) :
    coverRestrictionObject 𝒰 T i ⟶ T :=
  MorphismProperty.Over.homMk (pullback.fst T.hom (𝒰.f i)) pullback.condition

private lemma coverRestrictionSieve_mem (T : X.Etale) :
    Sieve.ofArrows (coverRestrictionObject 𝒰 T) (coverRestrictionMap 𝒰 T) ∈
      X.smallEtaleTopology T := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  exact Scheme.Cover.iUnion_range (𝒰.pullback₁ T.hom)

/-- Bijectivity on every member of a base étale cover detects isomorphisms
of set-valued sheaves on the small étale site. -/
lemma isIso_of_bijective_on_etaleCover
    {F G : Sheaf X.smallEtaleTopology (Type u)} (η : F ⟶ G)
    (h : ∀ (i : 𝒰.I₀) (T : (𝒰.X i).Etale),
      Function.Bijective (η.hom.app (op ((etalePostcompose (𝒰.f i)).obj T)))) :
    IsIso η := by
  have hInjective : Presheaf.IsLocallyInjective X.smallEtaleTopology η.hom := by
    refine ⟨?_⟩
    intro T x y hxy
    apply X.smallEtaleTopology.superset_covering ?_ (coverRestrictionSieve_mem 𝒰 T.unop)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    change F.obj.map (coverRestrictionMap 𝒰 T.unop i).op x =
      F.obj.map (coverRestrictionMap 𝒰 T.unop i).op y
    apply (h i ((etaleBaseChange (𝒰.f i)).obj T.unop)).injective
    change η.hom.app (op (coverRestrictionObject 𝒰 T.unop i))
        (F.obj.map (coverRestrictionMap 𝒰 T.unop i).op x) =
      η.hom.app (op (coverRestrictionObject 𝒰 T.unop i))
        (F.obj.map (coverRestrictionMap 𝒰 T.unop i).op y)
    rw [η.hom.naturality_apply, η.hom.naturality_apply, hxy]
  have hSurjective : Presheaf.IsLocallySurjective X.smallEtaleTopology η.hom := by
    refine ⟨?_⟩
    intro T s
    apply X.smallEtaleTopology.superset_covering ?_ (coverRestrictionSieve_mem 𝒰 T)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (h i ((etaleBaseChange (𝒰.f i)).obj T)).surjective
      (G.obj.map (coverRestrictionMap 𝒰 T i).op s)
  exact (Sheaf.isLocallyBijective_iff_isIso η).mp ⟨hInjective, hSurjective⟩

section Sigma

variable {ι : Type v} [Small.{u} ι] (U : ι → X.Etale)

/-- The disjoint union of étale objects, with its induced map to the base. -/
def etaleSigma : X.Etale := by
  let : IsZariskiLocalAtSource (show MorphismProperty Scheme.{u} from @Etale) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact MorphismProperty.Over.mk ⊤ (Sigma.desc (fun i => (U i).hom))
    (IsZariskiLocalAtSource.sigmaDesc (fun i => (U i).prop))

/-- Inclusion of one component into the disjoint union on the small étale site. -/
def etaleSigmaInj (i : ι) : U i ⟶ etaleSigma U :=
  MorphismProperty.Over.homMk (Sigma.ι (fun j => (U j).left) i)
    (Sigma.ι_comp_desc (fun j => (U j).hom) i)

private def isInitialEtaleOfEmpty (T : X.Etale) [IsEmpty T.left] : IsInitial T := by
  let hT : IsInitial T.left := isInitialOfIsEmpty
  let : ∀ V : X.Etale, Unique (T ⟶ V) := fun V =>
    { default := MorphismProperty.Over.homMk (hT.to V.left) (hT.hom_ext _ _)
      uniq f := MorphismProperty.Over.Hom.ext (hT.hom_ext _ _) }
  exact IsInitial.ofUnique T

private lemma emptyEtaleCover (T : X.Etale) (hT : IsInitial T) :
    ⊥ ∈ X.smallEtaleTopology T := by
  let E : X.Etale := MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) inferInstance
  have : IsEmpty T.left :=
    ⟨fun t => isEmptyElim (show (∅ : Scheme.{u}) from (hT.to E).left t)⟩
  have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff
    (Z := fun i : PEmpty.{1} => i.elim) (W := T) (fun i => i.elim)).mpr
      (by ext t; exact isEmptyElim t)
  simpa only [Sieve.ofArrows, Presieve.ofArrows_of_isEmpty, Sieve.generate_bot] using h

/-- Disjoint unions of étale objects give coproducts of their represented sheaves. -/
def etaleSigmaYonedaIsColimit :
    IsColimit (Cofan.mk (X.smallEtaleTopology.yoneda.obj (etaleSigma U))
      (fun i => X.smallEtaleTopology.yoneda.map (etaleSigmaInj U i))) := by
  have (i : ι) : Mono ((Cofan.mk (etaleSigma U) (etaleSigmaInj U)).inj i) := by
    constructor
    intro T a b hab
    apply MorphismProperty.Over.Hom.ext
    exact (cancel_mono (Sigma.ι (fun j => (U j).left) i)).mp
      (congrArg (fun f => f.left) hab)
  apply X.smallEtaleTopology.isColimitCofanMkYoneda U
    (c := Cofan.mk (etaleSigma U) (etaleSigmaInj U))
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Scheme.Cover.iUnion_range (sigmaOpenCover (fun i => (U i).left))
  · exact emptyEtaleCover
  · intro i j hij T a b hab
    have : IsEmpty T.left := isEmpty_of_commSq_sigmaι_of_ne
      ⟨congrArg (fun f => f.left) hab⟩ hij
    exact ⟨isInitialEtaleOfEmpty T⟩

/-- The Yoneda morphism obtained by gluing a family of sections on disjoint components. -/
def etaleSigmaSheafHom (G : Sheaf X.smallEtaleTopology (Type u))
    (s : ∀ i : ι, G.obj.obj (op (U i))) :
    X.smallEtaleTopology.yoneda.obj (etaleSigma U) ⟶ G :=
  (etaleSigmaYonedaIsColimit U).desc
    (Cofan.mk G (fun i => X.smallEtaleTopology.yonedaEquiv.symm (s i)))

/-- The glued Yoneda morphism agrees with the specified section on each component. -/
lemma etaleSigmaSheafHom_comp (G : Sheaf X.smallEtaleTopology (Type u))
    (s : ∀ i : ι, G.obj.obj (op (U i))) (i : ι) :
    X.smallEtaleTopology.yoneda.map (etaleSigmaInj U i) ≫ etaleSigmaSheafHom U G s =
      X.smallEtaleTopology.yonedaEquiv.symm (s i) :=
  (etaleSigmaYonedaIsColimit U).fac
    (Cofan.mk G (fun j => X.smallEtaleTopology.yonedaEquiv.symm (s j))) ⟨i⟩

/-- Evaluation of the glued morphism on a map through one component. -/
lemma etaleSigmaSheafHom_apply_component (G : Sheaf X.smallEtaleTopology (Type u))
    (s : ∀ i : ι, G.obj.obj (op (U i))) (i : ι) {T : X.Etale} (f : T ⟶ U i) :
    (etaleSigmaSheafHom U G s).hom.app (op T) (f ≫ etaleSigmaInj U i) =
      G.obj.map f.op (s i) := by
  exact congrArg (fun k => k.hom.app (op T) f) (etaleSigmaSheafHom_comp U G s i)

/-- A family of sections on disjoint étale objects glues to a section on their union. -/
def etaleSigmaSection (G : Sheaf X.smallEtaleTopology (Type u))
    (s : ∀ i : ι, G.obj.obj (op (U i))) : G.obj.obj (op (etaleSigma U)) :=
  X.smallEtaleTopology.yonedaEquiv (etaleSigmaSheafHom U G s)

/-- Restriction of the glued section recovers each prescribed local section. -/
lemma etaleSigmaSection_restrict (G : Sheaf X.smallEtaleTopology (Type u))
    (s : ∀ i : ι, G.obj.obj (op (U i))) (i : ι) :
    G.obj.map (etaleSigmaInj U i).op (etaleSigmaSection U G s) = s i := by
  change G.obj.map (etaleSigmaInj U i).op
    (X.smallEtaleTopology.yonedaEquiv (etaleSigmaSheafHom U G s)) = s i
  rw [X.smallEtaleTopology.yonedaEquiv_naturality, etaleSigmaSheafHom_comp,
    Equiv.apply_symm_apply]

end Sigma

/-- The universal property of a Cartesian square, in the small étale categories. -/
lemma etalePostcompose_hom_bijective_of_isPullback
    {A B : Scheme.{u}} (f : A ⟶ B) [Etale f] (W : A.Etale) (V : B.Etale)
    (k : (etalePostcompose f).obj W ⟶ V)
    (h : IsPullback W.hom k.left f V.hom) (T : A.Etale) :
    Function.Bijective (fun g : T ⟶ W => (etalePostcompose f).map g ≫ k) := by
  constructor
  · intro g g' hgg'
    apply MorphismProperty.Over.Hom.ext
    apply h.hom_ext
    · exact g.w.trans g'.w.symm
    · exact congrArg (fun e => e.left) hgg'
  · intro g
    let l : T ⟶ W := MorphismProperty.Over.homMk
      (h.lift T.hom g.left g.w.symm) (h.lift_fst T.hom g.left g.w.symm)
    refine ⟨l, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    exact h.lift_snd T.hom g.left g.w.symm

/-- Local representers on the disjoint components represent the sheaf on the
whole disjoint union. No finiteness hypothesis on the family is required. -/
def sigmaRepresentableBy {ι : Type v} [Small.{u} ι] (U : ι → Scheme.{u})
    (G : Sheaf (∐ U).smallEtaleTopology (Type u)) (W : ∀ i : ι, (U i).Etale)
    (h : ∀ i : ι, ((etalePostcompose (Sigma.ι U i)).op ⋙ G.obj).RepresentableBy (W i)) :
    G.obj.RepresentableBy
      (etaleSigma (fun i => (etalePostcompose (Sigma.ι U i)).obj (W i))) := by
  let Z : ι → (∐ U).Etale := fun i => (etalePostcompose (Sigma.ι U i)).obj (W i)
  let s : ∀ i : ι, G.obj.obj (op (Z i)) := fun i => (h i).homEquiv (𝟙 (W i))
  let η := etaleSigmaSheafHom Z G s
  have hη : IsIso η := by
    apply isIso_of_bijective_on_etaleCover
      ((sigmaOpenCover U).changeProp (Q := show MorphismProperty Scheme.{u} from @Etale)
        (fun i => inferInstance)) η
    intro i T
    have hCart : IsPullback (W i).hom (etaleSigmaInj Z i).left
        (Sigma.ι U i) (etaleSigma Z).hom :=
      isPullback_sigmaι_sigmaMap (fun j => (W j).hom) i
    have hHom := etalePostcompose_hom_bijective_of_isPullback
      (Sigma.ι U i) (W i) (etaleSigma Z) (etaleSigmaInj Z i) hCart T
    apply (Function.Bijective.of_comp_iff _ hHom).mp
    have heq : (fun g : T ⟶ W i =>
        η.hom.app (op ((etalePostcompose (Sigma.ι U i)).obj T))
          ((etalePostcompose (Sigma.ι U i)).map g ≫ etaleSigmaInj Z i)) =
        (h i).homEquiv := by
      funext g
      exact (etaleSigmaSheafHom_apply_component Z G s i
        ((etalePostcompose (Sigma.ι U i)).map g)).trans
          ((h i).homEquiv_eq g).symm
    change Function.Bijective (fun g : T ⟶ W i =>
      η.hom.app (op ((etalePostcompose (Sigma.ι U i)).obj T))
        ((etalePostcompose (Sigma.ι U i)).map g ≫ etaleSigmaInj Z i))
    rw [heq]
    exact (h i).homEquiv.bijective
  exact Functor.representableByEquiv.symm
    ((sheafToPresheaf (∐ U).smallEtaleTopology (Type u)).mapIso (asIso η))

/-- Local representers of a sheaf on arbitrary étale objects combine to represent
its ordinary restriction to their disjoint union. -/
def etaleSigmaRestrictionRepresentableBy {ι : Type v} [Small.{u} ι]
    (U : ι → X.Etale) (G : Sheaf X.smallEtaleTopology (Type u))
    (W : ∀ i : ι, (U i).left.Etale)
    (h : ∀ i : ι, ((etalePostcompose (U i).hom).op ⋙ G.obj).RepresentableBy (W i)) :
    ((etalePostcompose (hf := (etaleSigma U).prop) (etaleSigma U).hom).op ⋙ G.obj).RepresentableBy
      (etaleSigma (fun i =>
        (etalePostcompose (Sigma.ι (fun j => (U j).left) i)).obj (W i))) := by
  apply sigmaRepresentableBy (fun i => (U i).left)
    ((etaleRestriction (hf := (etaleSigma U).prop) (etaleSigma U).hom (Type u)).obj G) W
  intro i
  let e : etalePostcompose (U i).hom ≅
      etalePostcompose (Sigma.ι (fun j => (U j).left) i) ⋙
        etalePostcompose (hf := (etaleSigma U).prop) (etaleSigma U).hom :=
    MorphismProperty.Over.mapComp
      (P := show MorphismProperty Scheme.{u} from @Etale) ⊤
      (inferInstance : Etale (Sigma.ι (fun j => (U j).left) i))
      (etaleSigma U).prop (U i).hom (Sigma.ι_comp_desc (fun j => (U j).hom) i).symm
  exact (h i).ofIso (Functor.isoWhiskerRight (NatIso.op e).symm G.obj)

/-- The finite étale scheme over a disjoint union obtained by taking the
disjoint union of the given finite étale schemes. The index set may be infinite. -/
def finiteEtaleSigma {ι : Type v} [Small.{u} ι] (U : ι → Scheme.{u})
    (W : ∀ i : ι, FiniteEtale (U i)) : FiniteEtale (∐ U) :=
  MorphismProperty.Over.mk ⊤ (Limits.Sigma.map (fun i => (W i).hom))
    (IsFiniteEtale.sigmaMap (fun i => (W i).hom))

/-- Finite étale local representers combine into an actual finite étale
representer after restricting to the disjoint union of the local bases. -/
def finiteEtaleSigmaRestrictionRepresentableBy {ι : Type v} [Small.{u} ι]
    (U : ι → X.Etale) (G : Sheaf X.smallEtaleTopology (Type u))
    (W : ∀ i : ι, FiniteEtale (U i).left)
    (h : ∀ i : ι, ((etalePostcompose (U i).hom).op ⋙ G.obj).RepresentableBy
      ((finiteEtaleToEtale (U i).left).obj (W i))) :
    ((etalePostcompose (hf := (etaleSigma U).prop) (etaleSigma U).hom).op ⋙ G.obj).RepresentableBy
      ((finiteEtaleToEtale (etaleSigma U).left).obj
        (finiteEtaleSigma (fun i => (U i).left) W)) :=
  etaleSigmaRestrictionRepresentableBy U G
    (fun i => (finiteEtaleToEtale (U i).left).obj (W i)) h

end EtaleCohomology
