/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ClosedAdjunction
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Nyll.SchemeTheory.Etale.ProperLocalCover
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic


/-!
# Injectivity of proper-local restriction on global sections

The actual inverse-image/direct-image unit is an isomorphism on geometric
stalks along a closed immersion. Equal images of two global sections
therefore give equal germs at the closed fiber, and the filtered-colimit
description supplies étale neighborhoods on which the sections agree.

Choose one such neighborhood for each point of the closed fiber. This is a
family in the original universe. Proper-local covering detection makes
its disjoint union surjective, and the sheaf separation axiom proves equality
of the original sections. Only universally closedness of the structure
morphism is needed. Surjectivity of restriction and positive-degree proper
base change are not asserted.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem covering_sieve_of_closedFiber
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (S : Sieve (Scheme.Etale.mk (𝟙 X)))
    (hS : ∀ x : X, f x = IsLocalRing.closedPoint R →
      ∃ (V : X.Etale) (g : V ⟶ Scheme.Etale.mk (𝟙 X)) (v : V.left),
        S g ∧ g.left v = x) :
    S ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  classical
  let I : Type u := {x : X // f x = IsLocalRing.closedPoint R}
  choose V g v hg hv using fun x : I => hS x.1 x.2
  let p : (∐ fun x : I => (V x).left) ⟶ X :=
    Sigma.desc (fun x : I => (g x).left)
  have hpι (x : I) (a : (V x).left) :
      p (Sigma.ι (fun x : I => (V x).left) x a) = (g x).left a := by
    exact (Scheme.Hom.comp_apply _ _ a).symm.trans
      (congrArg (fun k : (V x).left ⟶ X => k a)
        (Sigma.ι_comp_desc (fun x : I => (g x).left) x))
  have : Etale p := by
    have : IsZariskiLocalAtSource (show MorphismProperty Scheme.{u} from @Etale) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (fun x : I => inferInstanceAs (Etale (g x).left))
  have : Surjective p := Etale.surjective_of_closedFiber_subset_range R f p (by
    intro x hx
    refine ⟨Sigma.ι (fun x : I => (V x).left) ⟨x, hx⟩ (v ⟨x, hx⟩), ?_⟩
    exact (hpι ⟨x, hx⟩ (v ⟨x, hx⟩)).trans (hv ⟨x, hx⟩))
  have hcover : Sieve.ofArrows V g ∈ X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨t, ht⟩ := p.surjective x
    obtain ⟨j, a, ha⟩ : ∃ (j : I) (a : (V j).left),
        Sigma.ι (fun x : I => (V x).left) j a = t :=
      (AlgebraicGeometry.sigmaOpenCover (fun x : I => (V x).left)).exists_eq t
    exact Set.mem_iUnion.mpr ⟨j, a, (hpι j a).symm.trans ((congrArg p ha).trans ht)⟩
  apply X.smallEtaleTopology.superset_covering (R := S) ?_ hcover
  intro Y k hk
  obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff V g k).mp hk
  exact S.downward_closed (hg j) a

private theorem exists_neighborhood_unit_sections_eq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (a b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (hab : (((etalePullbackPushforwardAdjunction i Λ).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))) a =
      (((etalePullbackPushforwardAdjunction i Λ).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X)))) b)
    (z : Z) :
    ∃ (V : X.Etale) (g : V ⟶ Scheme.Etale.mk (𝟙 X)) (v : V.left),
      F.obj.map g.op a = F.obj.map g.op b ∧ g.left v = i z := by
  let Ω : Type u := SeparableClosure (Z.residueField z)
  let s : Spec (CommRingCat.of Ω) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫
      Z.fromSpecResidueField z
  let ξ : Spec (CommRingCat.of Ω) := default
  have hs : s ξ = z := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply z _
  let Φ : X.smallEtaleTopology.Point := Scheme.pointSmallEtale (s ≫ i)
  let W : X.Etale := Scheme.Etale.mk (𝟙 X)
  let w : Φ.fiber.obj W := Over.homMk (s ≫ i) (Category.comp_id (s ≫ i))
  let η : F ⟶ (etalePushforward i Λ).obj ((etalePullback i Λ).obj F) :=
    (etalePullbackPushforwardAdjunction i Λ).unit.app F
  have : IsIso (Φ.sheafFiber.map η) := etalePushforwardClosed_unit_stalk_isIso i Λ s F
  have hinj : Function.Injective (Φ.presheafFiber.map η.hom) :=
    (ModuleCat.mono_iff_injective _).mp (show Mono (Φ.sheafFiber.map η) from inferInstance)
  have heq : Φ.toPresheafFiber W w F.obj a = Φ.toPresheafFiber W w F.obj b := by
    apply hinj
    rw [Φ.toPresheafFiber_naturality_apply, Φ.toPresheafFiber_naturality_apply, hab]
  obtain ⟨V, g, y, _, hy⟩ := (Φ.toPresheafFiber_eq_iff' W w a b).mp heq
  let t : Spec (CommRingCat.of Ω) ⟶ V.left := y.left
  have ht : t ≫ V.hom = s ≫ i := y.w
  refine ⟨V, g, t ξ, hy, ?_⟩
  have hgleft : g.left = V.hom := by
    have h := g.w
    change g.left ≫ 𝟙 X = V.hom at h
    exact (Category.comp_id g.left).symm.trans h
  have hyp : V.hom (t ξ) = (s ≫ i) ξ :=
    (Scheme.Hom.comp_apply t V.hom ξ).symm.trans
      (congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ X => k ξ) ht)
  exact (congrArg (fun k : V.left ⟶ X => k (t ξ)) hgleft).trans
    (hyp.trans ((Scheme.Hom.comp_apply s i ξ).trans (congrArg i hs)))

/-- For a universally closed scheme over a local ring, restriction to the
actual closed fiber is injective on global sections of every coefficient sheaf.
The map is the existing inverse-image/direct-image unit evaluated on the
identity object of the small étale site. In particular it applies to proper
schemes, with no henselian, noetherian or torsion requirement. -/
theorem etaleClosedFiber_unit_globalSections_injective
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (Λ : Type u) [CommRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Injective
      (((etalePullbackPushforwardAdjunction
        (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
          Λ).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 X)))) := by
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let i : pullback f r ⟶ X := pullback.fst f r
  have : IsClosedImmersion r := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (IsLocalRing.residue R)) IsLocalRing.residue_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst f r))
  intro a b hab
  have hcover : Presheaf.equalizerSieve (F := F.obj) a b ∈
      X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
    apply covering_sieve_of_closedFiber R f
    intro x hx
    let x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) := default
    have hr : r x₀ = IsLocalRing.closedPoint R :=
      IsLocalRing.PrimeSpectrum.comap_residue R x₀
    obtain ⟨z, hzx, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := r) x x₀ (hx.trans hr.symm)
    obtain ⟨V, g, v, hEq, hv⟩ := exists_neighborhood_unit_sections_eq i Λ F a b hab z
    exact ⟨V, g, v, hEq, hv.trans hzx⟩
  have : X.smallEtaleTopology.HasSheafCompose (forget (ModuleCat.{u} Λ)) := by
    let : PreservesLimitsOfSize.{u, u + 1} (forget (ModuleCat.{u} Λ)) :=
      (ModuleCat.adj Λ).rightAdjoint_preservesLimits
    exact hasSheafCompose_of_preservesLimitsOfSize
      (F := forget (ModuleCat.{u} Λ)) X.smallEtaleTopology
  exact F.isSeparated (Scheme.Etale.mk (𝟙 X)) (Presheaf.equalizerSieve (F := F.obj) a b)
    hcover a b (fun _ _ h => h)

end EtaleCohomology
