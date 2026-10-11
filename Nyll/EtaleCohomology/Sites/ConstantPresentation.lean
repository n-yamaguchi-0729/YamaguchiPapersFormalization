/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ConstantRepresentable
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Local factorization of finitely generated constant modules

A map from a constant presheaf of finitely generated modules locally factors
through any locally bijective constant presentation of its target. A finite
intersection of covering image sieves puts all generators in the image. On
a neighborhood containing a chosen point, local injectivity of the constant
presentation is genuine injectivity, so the resulting lift is linear.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Opposite

namespace EtaleCohomology

/-- Every point has a neighborhood belonging to a covering sieve of the small étale site. -/
lemma exists_etale_neighborhood_in_sieve {X : Scheme.{u}} {W : X.Etale}
    (S : Sieve W) (hS : S ∈ X.smallEtaleTopology W) (x : W.left) :
    ∃ (Y : X.Etale) (g : Y ⟶ W) (y : Y.left), S g ∧ g.left y = x := by
  have h : S ∈ (X.smallPretopology (P := show MorphismProperty Scheme.{u} from @Etale)
      (Q := show MorphismProperty Scheme.{u} from @Etale)).toGrothendieck W := by
    rw [← Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X (le_refl _)]
    exact hS
  obtain ⟨Y, g, y, hg, _, hy⟩ := (Scheme.mem_toGrothendieck_smallPretopology
    (P := show MorphismProperty Scheme.{u} from @Etale)
    (Q := show MorphismProperty Scheme.{u} from @Etale) W S).mp h x
  exact ⟨Y, g, y, hg, hy⟩

private lemma finset_inf_cover {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {W : C} {ι : Type*}
    (s : Finset ι) (S : ι → Sieve W) (hS : ∀ i ∈ s, S i ∈ J W) :
    s.inf S ∈ J W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact J.top_mem W
  | @insert a s ha ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hS a (Finset.mem_insert_self a s))
      (ih (fun i hi => hS i (Finset.mem_insert_of_mem hi)))

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- A locally injective constant presentation is injective on every nonempty étale object. -/
lemma constantPresentation_app_injective
    {M : ModuleCat.{u} R} {F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R}
    (η : (Functor.const X.Etaleᵒᵖ).obj M ⟶ F)
    [Presheaf.IsLocallyInjective X.smallEtaleTopology η]
    (W : X.Etale) (x : W.left) : Function.Injective (η.app (op W)) := by
  intro a b hab
  obtain ⟨Y, g, _, hg, _⟩ := exists_etale_neighborhood_in_sieve
    (Presheaf.equalizerSieve (F := (Functor.const X.Etaleᵒᵖ).obj M) (X := op W) a b)
    (Presheaf.equalizerSieve_mem X.smallEtaleTopology η a b hab) x
  exact hg

/-- Finitely many generators can be lifted on one actual étale neighborhood,
and local injectivity makes the lift a module homomorphism. -/
theorem exists_constantPresentation_factor
    (M N : ModuleCat.{u} R) [Module.Finite R M]
    {F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R}
    (α : (Functor.const X.Etaleᵒᵖ).obj M ⟶ F)
    (η : (Functor.const X.Etaleᵒᵖ).obj N ⟶ F)
    [Presheaf.IsLocallyInjective X.smallEtaleTopology η]
    [Presheaf.IsLocallySurjective X.smallEtaleTopology η]
    (x : X) : ∃ (Y : X.Etale) (y : Y.left) (l : M ⟶ N),
      Y.hom y = x ∧ α.app (op Y) = l ≫ η.app (op Y) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let W : X.Etale := etaleBaseObject X
  let S : Fin n → Sieve W := fun i => Presheaf.imageSieve η ((α.app (op W)) (s i))
  have hS : Finset.univ.inf S ∈ X.smallEtaleTopology W :=
    finset_inf_cover X.smallEtaleTopology Finset.univ S
      (fun i _ => Presheaf.imageSieve_mem X.smallEtaleTopology η ((α.app (op W)) (s i)))
  obtain ⟨Y, g, y, hg, hy⟩ := exists_etale_neighborhood_in_sieve (Finset.univ.inf S) hS x
  have hgen : ∀ i : Fin n, (α.app (op Y)) (s i) ∈ LinearMap.range (η.app (op Y)).hom := by
    intro i
    have hgi : S i g := (Finset.inf_le (Finset.mem_univ i) : Finset.univ.inf S ≤ S i) g hg
    obtain ⟨z, hz⟩ := hgi
    refine ⟨z, ?_⟩
    exact hz.trans (NatTrans.naturality_apply α g.op (s i)).symm
  have hrange : ∀ m : M, (α.app (op Y)) m ∈ LinearMap.range (η.app (op Y)).hom := by
    have htop : (⊤ : Submodule R M) ≤
        (LinearMap.range (η.app (op Y)).hom).comap (α.app (op Y)).hom := by
      rw [← hs]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hgen i
    intro m
    exact htop (Submodule.mem_top : m ∈ (⊤ : Submodule R M))
  let e : N ≃ₗ[R] LinearMap.range (η.app (op Y)).hom :=
    LinearEquiv.ofInjective (η.app (op Y)).hom (constantPresentation_app_injective η Y y)
  let l : M ⟶ N := ModuleCat.ofHom
    (e.symm.toLinearMap.comp ((α.app (op Y)).hom.codRestrict _ hrange))
  refine ⟨Y, y, l, ?_, ?_⟩
  · have hw : g.left ≫ W.hom = Y.hom := g.w
    have hp := congrArg (fun k : Y.left ⟶ X => k y) hw
    exact hp.symm.trans hy
  · ext m
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨(α.app (op Y)) m, hrange m⟩)).symm

/-- A map from a finite free constant presheaf locally lifts through a locally
surjective morphism, by lifting the finitely many basis vectors simultaneously. -/
theorem exists_constantFreePresentation_lift (n : ℕ)
    {G H : X.Etaleᵒᵖ ⥤ ModuleCat.{u} R}
    (α : (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R (Fin n →₀ R)) ⟶ H)
    (η : G ⟶ H) [Presheaf.IsLocallySurjective X.smallEtaleTopology η]
    (x : X) : ∃ (Y : X.Etale) (y : Y.left)
      (l : ModuleCat.of R (Fin n →₀ R) ⟶ G.obj (op Y)),
      Y.hom y = x ∧ l ≫ η.app (op Y) = α.app (op Y) := by
  classical
  let W : X.Etale := etaleBaseObject X
  let S : Fin n → Sieve W := fun i =>
    Presheaf.imageSieve η ((α.app (op W)) (Finsupp.single i 1))
  have hS : Finset.univ.inf S ∈ X.smallEtaleTopology W :=
    finset_inf_cover X.smallEtaleTopology Finset.univ S
      (fun i _ => Presheaf.imageSieve_mem X.smallEtaleTopology η _)
  obtain ⟨Y, g, y, hg, hy⟩ := exists_etale_neighborhood_in_sieve (Finset.univ.inf S) hS x
  have hgen : ∀ i : Fin n, ∃ z : G.obj (op Y),
      (η.app (op Y)) z = (α.app (op Y)) (Finsupp.single i 1) := by
    intro i
    have hgi : S i g := (Finset.inf_le (Finset.mem_univ i) : Finset.univ.inf S ≤ S i) g hg
    obtain ⟨z, hz⟩ := hgi
    exact ⟨z, hz.trans (NatTrans.naturality_apply α g.op (Finsupp.single i 1)).symm⟩
  choose z hz using hgen
  let l : ModuleCat.of R (Fin n →₀ R) ⟶ G.obj (op Y) :=
    ModuleCat.ofHom (Finsupp.linearCombination R z)
  refine ⟨Y, y, l, ?_, ?_⟩
  · have hp := congrArg (fun k : Y.left ⟶ X => k y) g.w
    exact hp.symm.trans hy
  · apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro i r
    change (η.app (op Y)) (Finsupp.linearCombination R z (Finsupp.single i r)) =
      (α.app (op Y)) (Finsupp.single i r)
    rw [Finsupp.linearCombination_single, map_smul, hz,
      ← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
end EtaleCohomology
