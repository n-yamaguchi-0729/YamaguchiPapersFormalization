/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Nyll.AlgebraicCurves.Hilbert.SymmetricPowerData
import Mathlib.Data.List.FinRange
import Mathlib.Data.Multiset.MapFold

/-!
# Finite sums towards the Albanese construction

A morphism from a scheme to a relative group defines a sum morphism on every finite
power of the source. Its action on test schemes is natural. Over an arbitrary field,
properness and geometric integrality of the target imply permutation invariance:
commutativity is deduced from the existing geometric theorem, not assumed.
The list sum therefore descends to multisets of test-scheme points, naturally in the
test scheme. This is a quotient of point families, not an assertion of a scheme quotient.

The construction does not require a rational point or algebraic closedness of the field.
It does not yet assert invariance under linear equivalence or descent to a Jacobian.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)}

/-- Add an ordered finite list of relative points using the given group law. -/
def sumList (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (xs : List (SchemeHomOver t f)) :
    SchemeHomOver t f :=
  xs.foldr (G.mul t) (G.one t)

/-- The sum of an empty list is the identity point. -/
theorem sumList_nil (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : G.sumList t [] = G.one t :=
  List.foldr_nil

/-- Adding a head to a list multiplies its value by the sum of the tail. -/
theorem sumList_cons (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f)
    (xs : List (SchemeHomOver t f)) :
    G.sumList t (x :: xs) = G.mul t x (G.sumList t xs) :=
  List.foldr_cons

/-- Concatenating two lists adds their sums. -/
theorem sumList_append (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (xs ys : List (SchemeHomOver t f)) :
    G.sumList t (xs ++ ys) = G.mul t (G.sumList t xs) (G.sumList t ys) := by
  induction xs with
  | nil => exact (G.one_mul t (G.sumList t ys)).symm
  | cons x xs ih =>
    rw [List.cons_append, sumList_cons, sumList_cons, ih, G.mul_assoc]

/-- The finite sum commutes with pullback along a morphism of test schemes. -/
theorem sumList_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (xs : List (SchemeHomOver t f)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.sumList t xs) =
      G.sumList t' (xs.map (GoodReductionJacobian.schemeHomOverComp ψ hψ)) := by
  induction xs with
  | nil => exact G.one_natural t t' ψ hψ
  | cons x xs ih =>
    rw [sumList_cons, List.map_cons, sumList_cons, G.mul_natural, ih]

/-- The sum of a finite family of morphisms to the relative group, as an actual morphism. -/
def sumFamily (G : RelativeGroupLaw R f) (T : Over (Spec (CommRingCat.of R)))
    {n : ℕ} (xs : Fin n → (T ⟶ Over.mk f)) : T ⟶ Over.mk f :=
  (overHomEquivSchemeHomOver T f).symm
    (G.sumList T.hom (List.ofFn fun i => overHomEquivSchemeHomOver T f (xs i)))

/-- The finite-family sum is natural in the test scheme. -/
theorem sumFamily_natural (G : RelativeGroupLaw R f)
    {T T' : Over (Spec (CommRingCat.of R))} (ψ : T' ⟶ T)
    {n : ℕ} (xs : Fin n → (T ⟶ Over.mk f)) :
    ψ ≫ G.sumFamily T xs = G.sumFamily T' (fun i => ψ ≫ xs i) := by
  apply (overHomEquivSchemeHomOver T' f).injective
  change GoodReductionJacobian.schemeHomOverComp ψ.left (Over.w ψ)
    (G.sumList T.hom (List.ofFn fun i => overHomEquivSchemeHomOver T f (xs i))) =
      G.sumList T'.hom
        (List.ofFn fun i => overHomEquivSchemeHomOver T' f (ψ ≫ xs i))
  rw [G.sumList_natural, List.map_ofFn]
  rfl

section Field

variable {K : Type u} [Field K] {B : Scheme.{u}}
  {b : B ⟶ Spec (CommRingCat.of K)}

/-- Add the images of the coordinates on the existing finite fibre power of the source scheme. -/
def finiteSumMap (G : RelativeGroupLaw K b) {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (q : SchemeHomOver c b) (n : ℕ) :
    SchemeHomOver (finFibrePow.toBase c n) b :=
  G.sumList (finFibrePow.toBase c n) (List.ofFn fun i : Fin n =>
    NeronModelInfra.schemeHomOverComp
      ⟨finFibrePow.proj c n i, finFibrePow.proj_comp c n i⟩ q)

/-- Evaluating the sum morphism at a family of points adds their images. -/
theorem finiteSumMap_evaluate (G : RelativeGroupLaw K b) {C T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (q : SchemeHomOver c b) {n : ℕ}
    (t : T ⟶ Spec (CommRingCat.of K)) (xs : Fin n → SchemeHomOver t c) :
    GoodReductionJacobian.schemeHomOverComp
        (WidePullback.lift t (fun i => (xs i).1) (fun i => (xs i).2))
        (WidePullback.lift_base _ _ _ _) (G.finiteSumMap c q n) =
      G.sumList t (List.ofFn fun i => NeronModelInfra.schemeHomOverComp (xs i) q) := by
  rw [finiteSumMap, sumList_natural, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply Subtype.ext
  change WidePullback.lift t (fun j => (xs j).1) (fun j => (xs j).2) ≫
    (finFibrePow.proj c n i ≫ q.1) = (xs i).1 ≫ q.1
  exact WidePullback.lift_π_assoc _ _ _ _ _ _

variable [IsProper b] [GeometricallyIntegral b]

/-- Proper geometrically integral group targets make list sums invariant under permutation. -/
theorem sumList_perm (G : RelativeGroupLaw K b) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) {xs ys : List (SchemeHomOver t b)}
    (h : xs.Perm ys) : G.sumList t xs = G.sumList t ys := by
  induction h with
  | nil => rfl
  | cons x h ih => rw [sumList_cons, sumList_cons, ih]
  | swap x y xs =>
    rw [sumList_cons, sumList_cons, sumList_cons, sumList_cons,
      ← G.mul_assoc, ← G.mul_assoc,
      G.mul_comm_of_isProper_of_geometricallyIntegral t y x]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A finite-family sum over an arbitrary field is unchanged by reindexing its coordinates. -/
theorem sumFamily_perm (G : RelativeGroupLaw K b)
    (T : Over (Spec (CommRingCat.of K))) {n : ℕ}
    (xs : Fin n → (T ⟶ Over.mk b)) (σ : Equiv.Perm (Fin n)) :
    G.sumFamily T (xs ∘ σ) = G.sumFamily T xs := by
  apply congrArg (overHomEquivSchemeHomOver T b).symm
  exact G.sumList_perm T.hom
    (σ.ofFn_comp_perm (fun i => overHomEquivSchemeHomOver T b (xs i)))

/-- The actual sum morphism is invariant under the existing action on the finite fibre power. -/
theorem finiteSumMap_permute (G : RelativeGroupLaw K b) {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) (q : SchemeHomOver c b) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    (finFibrePow.permAct c n σ).hom ≫ (G.finiteSumMap c q n).1 =
      (G.finiteSumMap c q n).1 := by
  have h := G.sumList_natural (finFibrePow.toBase c n) (finFibrePow.toBase c n)
    (finFibrePow.permAct c n σ).hom (finFibrePow.permAct_hom_toBase c n σ)
    (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp
      ⟨finFibrePow.proj c n i, finFibrePow.proj_comp c n i⟩ q)
  rw [List.map_ofFn] at h
  have heq (i : Fin n) :
      GoodReductionJacobian.schemeHomOverComp (finFibrePow.permAct c n σ).hom
          (finFibrePow.permAct_hom_toBase c n σ)
          (NeronModelInfra.schemeHomOverComp
            ⟨finFibrePow.proj c n i, finFibrePow.proj_comp c n i⟩ q) =
        NeronModelInfra.schemeHomOverComp
          ⟨finFibrePow.proj c n (σ⁻¹ i), finFibrePow.proj_comp c n (σ⁻¹ i)⟩ q := by
    apply Subtype.ext
    change (finFibrePow.permAct c n σ).hom ≫ (finFibrePow.proj c n i ≫ q.1) = _
    rw [← Category.assoc, finFibrePow.permAct_hom, finFibrePow.permHom_proj]
    rfl
  have hc := congrArg
    (fun a : Fin n → SchemeHomOver (finFibrePow.toBase c n) b =>
      G.sumList (finFibrePow.toBase c n) (List.ofFn a)) (funext heq)
  have hp := G.sumList_perm (finFibrePow.toBase c n)
    ((σ⁻¹).ofFn_comp_perm (fun i : Fin n => NeronModelInfra.schemeHomOverComp
      ⟨finFibrePow.proj c n i, finFibrePow.proj_comp c n i⟩ q))
  exact congrArg Subtype.val (h.trans (hc.trans hp))

/-- Add an unordered finite family of test-scheme points.
The value is independent of the representing list by geometric commutativity. -/
def sumMultiset (G : RelativeGroupLaw K b) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (xs : Multiset (SchemeHomOver t b)) :
    SchemeHomOver t b :=
  Quot.liftOn xs (G.sumList t) (fun _ _ h => G.sumList_perm t h)

/-- The sum of a list represents its unordered sum. -/
theorem sumMultiset_coe (G : RelativeGroupLaw K b) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (xs : List (SchemeHomOver t b)) :
    G.sumMultiset t (xs : Multiset (SchemeHomOver t b)) = G.sumList t xs :=
  rfl

/-- Pulling an unordered family back to another test scheme commutes with its sum. -/
theorem sumMultiset_natural (G : RelativeGroupLaw K b) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (t' : T' ⟶ Spec (CommRingCat.of K))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (xs : Multiset (SchemeHomOver t b)) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.sumMultiset t xs) =
      G.sumMultiset t' (xs.map (GoodReductionJacobian.schemeHomOverComp ψ hψ)) := by
  refine Quot.inductionOn xs ?_
  intro ys
  exact G.sumList_natural t t' ψ hψ ys

/-- Union of unordered families adds their sums. -/
theorem sumMultiset_add (G : RelativeGroupLaw K b) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (xs ys : Multiset (SchemeHomOver t b)) :
    G.sumMultiset t (xs + ys) = G.mul t (G.sumMultiset t xs) (G.sumMultiset t ys) := by
  refine Quot.inductionOn xs ?_
  intro xs
  refine Quot.inductionOn ys ?_
  intro ys
  exact G.sumList_append t xs ys

end Field

end GoodReductionJacobian.RelativeGroupLaw
