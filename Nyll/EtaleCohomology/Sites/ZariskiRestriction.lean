/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Actual Zariski restriction of a small étale sheaf

The existing open-subscheme functor lifts to the small étale site. Taking
the open image of an étale morphism is left adjoint to this inclusion.
The inclusion preserves covering sieves, hence is continuous, and ordinary
presheaf restriction gives the actual sheaf on the underlying space.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace EtaleCohomology

variable (X : Scheme.{u})

/-- The existing open-subscheme functor, valued in the small étale site. -/
def zariskiToEtale : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U => inferInstanceAs (Etale U.ι)) (fun _ => trivial) (fun _ => trivial)

/-- The actual open image of an étale object. -/
def etaleOpenImage : X.Etale ⥤ X.Opens where
  obj U := ⟨Set.range U.hom, U.hom.isOpenMap.isOpen_range⟩
  map {U V} g := homOfLE (by
    rintro x ⟨u, rfl⟩
    exact ⟨g.left u, (Scheme.Hom.comp_apply g.left V.hom u).symm.trans
      (congrArg (fun h : U.left ⟶ X => h u) g.w)⟩)

private lemma hom_to_zariskiToEtale_eq {U : X.Opens} {T : X.Etale}
    (a b : T ⟶ (zariskiToEtale X).obj U) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono U.ι).mp
  exact a.w.trans b.w.symm

private def openImageHomEquiv (T : X.Etale) (U : X.Opens) :
    ((etaleOpenImage X).obj T ⟶ U) ≃ (T ⟶ (zariskiToEtale X).obj U) where
  toFun h := by
    have hRange : Set.range (T.hom : T.left ⟶ X) ⊆ Set.range (U.ι : U.toScheme ⟶ X) := by
      rw [Scheme.Opens.range_ι]
      exact h.le
    let k : T.left ⟶ U.toScheme :=
      IsOpenImmersion.lift (X := U.toScheme) (Y := T.left) (Z := X) U.ι T.hom hRange
    exact MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤) k
      (IsOpenImmersion.lift_fac U.ι T.hom hRange)
  invFun k := homOfLE (by
    rintro x ⟨t, rfl⟩
    have hk : U.ι (k.left t) = T.hom t :=
      (Scheme.Hom.comp_apply k.left U.ι t).symm.trans
        (congrArg (fun h : T.left ⟶ X => h t) k.w)
    rw [← hk]
    exact (k.left t).property)
  left_inv _ := Subsingleton.elim _ _
  right_inv k := hom_to_zariskiToEtale_eq X _ k

/-- An étale object maps into an open subscheme exactly when its open image
is contained in that open. -/
def etaleOpenImageAdjunction : etaleOpenImage X ⊣ zariskiToEtale X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := openImageHomEquiv X
      homEquiv_naturality_left_symm := fun _ _ => Subsingleton.elim _ _
      homEquiv_naturality_right := fun _ _ => hom_to_zariskiToEtale_eq X _ _ }

instance zariskiToEtale_isRightAdjoint : (zariskiToEtale X).IsRightAdjoint where
  exists_leftAdjoint := ⟨etaleOpenImage X, ⟨etaleOpenImageAdjunction X⟩⟩

/-- An actual covering sieve of opens is a covering sieve in the small
étale site after inclusion. -/
lemma zariskiToEtale_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology X) X.smallEtaleTopology
      (zariskiToEtale X) where
  cover_preserve {U} {S} hS := by
    let I := Σ V : X.Opens, {g : V ⟶ U // S g}
    let V : I → X.Etale := fun a => (zariskiToEtale X).obj a.1
    let g : ∀ a : I, V a ⟶ (zariskiToEtale X).obj U :=
      fun a => (zariskiToEtale X).map a.2.1
    have hCover : Sieve.ofArrows V g ∈ X.smallEtaleTopology ((zariskiToEtale X).obj U) := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨W, hWU, hS, hxW⟩ := hS x.val x.property
      refine Set.mem_iUnion.mpr ⟨⟨W, hWU, hS⟩, ⟨x.val, hxW⟩, ?_⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply hWU.le ⟨x.val, hxW⟩
    apply X.smallEtaleTopology.superset_covering (R := S.functorPushforward (zariskiToEtale X))
      ?_ hCover
    intro T k hk
    obtain ⟨a, b, rfl⟩ := (Sieve.mem_ofArrows_iff V g k).mp hk
    exact (S.functorPushforward (zariskiToEtale X)).downward_closed
      (Sieve.image_mem_functorPushforward (zariskiToEtale X) S a.2.2) b

instance zariskiToEtale_isContinuous :
    (zariskiToEtale X).IsContinuous (Opens.grothendieckTopology X) X.smallEtaleTopology :=
  (Functor.isContinuous_iff_coverPreserving (F := zariskiToEtale X)
    (J := Opens.grothendieckTopology X) (K := X.smallEtaleTopology)).mpr
      (zariskiToEtale_coverPreserving X)

variable (A : Type v) [Category.{w} A]

/-- Restriction of the actual étale presheaf along open immersions, with its
sheaf condition supplied by continuity of the constructed inclusion. -/
def etaleZariskiRestriction :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (Opens.grothendieckTopology X) A :=
  (zariskiToEtale X).sheafPushforwardContinuous A
    (Opens.grothendieckTopology X) X.smallEtaleTopology

end EtaleCohomology
