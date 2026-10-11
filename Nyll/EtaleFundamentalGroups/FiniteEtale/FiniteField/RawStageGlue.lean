/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.RelativeGluing

/-!
# Gluing local models from recovered transitions
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace EtaleFundamentalGroups

variable {B S : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over B) (V : 𝒰.I₀ × 𝒰.I₀ → Over B)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))

include hV in
private theorem rawGluingInclusion_open (i j : 𝒰.I₀) : IsOpenImmersion (d i j).left :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hV i j).flip inferInstance

include hV in
private theorem rawGluingInclusion_mono (i j : 𝒰.I₀) : Mono (d i j) := by
  have : IsOpenImmersion (d i j).left := rawGluingInclusion_open 𝒰 A V d y ℓ hV i j
  apply (Over.forget B).mono_of_mono_map
  exact inferInstanceAs (Mono (d i j).left)

include hV in
private theorem rawGluingInclusion_isIso (i : 𝒰.I₀) : IsIso (d i i) := by
  have : IsIso ((Over.forget B).map (d i i)) := by
    change IsIso (d i i).left
    rw [← (hV i i).isoPullback_hom_fst]
    infer_instance
  exact isIso_of_reflects_iso (d i i) (Over.forget B)

variable (t : ∀ i j : 𝒰.I₀, V (i, j) ⟶ V (j, i))
variable (ht : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j = ℓ i j)

include hV in
/-- Preservation of the base gives the other chart structure equation. -/
theorem rawGluingTransition_structure
    (hS : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j ≫ 𝒰.f j =
      (d i j).left ≫ y i ≫ 𝒰.f i) (i j : 𝒰.I₀) :
    (t i j).left ≫ (d j i).left ≫ y j = ℓ i j := by
  apply (cancel_mono (𝒰.f j)).mp
  rw [Category.assoc, Category.assoc, hS]
  exact (hV i j).w

private abbrev rawGluingTriple (i j k : 𝒰.I₀) : Over B :=
  pullback (d i j) (d i k)

private def rawGluingTripleToOverlap (i j k : 𝒰.I₀) :
    rawGluingTriple 𝒰 A V d i j k ⟶ V (j, k) := by
  let r := (pullback.fst (d i j) (d i k)).left
  let s := (pullback.snd (d i j) (d i k)).left
  have hrs : r ≫ (d i j).left = s ≫ (d i k).left :=
    congrArg (fun q => (Over.forget B).map q) pullback.condition
  let g : (rawGluingTriple 𝒰 A V d i j k).left ⟶ (V (j, k)).left :=
    (hV j k).lift (r ≫ (t i j).left ≫ (d j i).left) (s ≫ ℓ i k)
      (by
        calc
          (r ≫ (t i j).left ≫ (d j i).left) ≫ (y j ≫ 𝒰.f j) =
              r ≫ ℓ i j ≫ 𝒰.f j := by
            simpa only [Category.assoc] using
              congrArg (fun q => r ≫ q ≫ 𝒰.f j) (ht i j)
          _ = (r ≫ (d i j).left) ≫ (y i ≫ 𝒰.f i) := by
            rw [Category.assoc, (hV i j).w]
          _ = (s ≫ (d i k).left) ≫ (y i ≫ 𝒰.f i) :=
            congrArg (fun q => q ≫ (y i ≫ 𝒰.f i)) hrs
          _ = (s ≫ ℓ i k) ≫ 𝒰.f k := by
            rw [Category.assoc, (hV i k).w, Category.assoc])
  refine Over.homMk g ?_
  rw [← Over.w (d j k), ← Category.assoc]
  dsimp only [g]
  rw [(hV j k).lift_fst]
  simp only [Category.assoc, Over.w]
  exact Over.w (pullback.fst (d i j) (d i k))

private def rawGluingTripleTransition (i j k : 𝒰.I₀) :
    rawGluingTriple 𝒰 A V d i j k ⟶ rawGluingTriple 𝒰 A V d j k i :=
  pullback.lift
    (rawGluingTripleToOverlap 𝒰 A V d y ℓ hV t ht i j k)
    (pullback.fst _ _ ≫ t i j)
    (by
      apply Over.OverMorphism.ext
      exact (hV j k).lift_fst _ _ _)

private theorem rawGluingTripleTransition_fac (i j k : 𝒰.I₀) :
    rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ t i j :=
  pullback.lift_snd _ _ _

variable {B' Z : Scheme.{u}} (ψ : B' ⟶ B)

/-- The actual coefficient pullback, followed by forgetting its structure map. -/
abbrev gluingRecoveryFunctor : Over B ⥤ Scheme.{u} :=
  Over.pullback ψ ⋙ Over.forget B'

local instance gluingRecoveryFunctor_faithful [Flat ψ] [Surjective ψ] :
    (gluingRecoveryFunctor ψ).Faithful := by
  let : ∀ (T : Scheme.{u}) (g : T ⟶ B), Epi (pullback.fst g ψ) :=
    fun T g => Flat.epi_of_flat_of_surjective (pullback.fst g ψ)
  infer_instance

variable (h : ∀ i : 𝒰.I₀, (gluingRecoveryFunctor ψ).obj (A i) ⟶ Z)
variable [∀ i : 𝒰.I₀, Mono (h i)]
variable (hrec : ∀ i j : 𝒰.I₀,
  (gluingRecoveryFunctor ψ).map (t i j) ≫ (gluingRecoveryFunctor ψ).map (d j i) ≫ h j =
    (gluingRecoveryFunctor ψ).map (d i j) ≫ h i)

variable (hinj : ∀ (T : Over B) (i j : 𝒰.I₀),
  Function.Injective ((gluingRecoveryFunctor ψ).map (X := T) (Y := V (i, j))))

include hV hrec hinj in
private theorem rawGluingTransition_id (i : 𝒰.I₀) : t i i = 𝟙 _ := by
  have : Mono (d i i) := rawGluingInclusion_mono 𝒰 A V d y ℓ hV i i
  apply hinj (V (i, i)) i i
  apply (cancel_mono ((gluingRecoveryFunctor ψ).map (d i i) ≫ h i)).mp
  rw [(gluingRecoveryFunctor ψ).map_id, Category.id_comp]
  exact hrec i i

omit [∀ i : 𝒰.I₀, Mono (h i)] in
include hrec in
private theorem rawGluingTripleTransition_chartMap (i j k : 𝒰.I₀) :
    (gluingRecoveryFunctor ψ).map (rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht i j k) ≫
      (gluingRecoveryFunctor ψ).map (pullback.fst _ _) ≫
        (gluingRecoveryFunctor ψ).map (d j k) ≫ h j =
    (gluingRecoveryFunctor ψ).map (pullback.fst _ _) ≫
      (gluingRecoveryFunctor ψ).map (d i j) ≫ h i := by
  let K := gluingRecoveryFunctor ψ
  have hw : K.map (pullback.fst (d j k) (d j i)) ≫ K.map (d j k) =
      K.map (pullback.snd (d j k) (d j i)) ≫ K.map (d j i) := by
    rw [← K.map_comp, ← K.map_comp, pullback.condition]
  change K.map _ ≫ K.map _ ≫ K.map _ ≫ h j = K.map _ ≫ K.map _ ≫ h i
  rw [reassoc_of% hw, ← Category.assoc
      (K.map (rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht i j k)),
    ← K.map_comp, rawGluingTripleTransition_fac, K.map_comp, Category.assoc, hrec]

include hrec hinj in
private theorem rawGluingTripleTransition_cocycle (i j k : 𝒰.I₀) :
    rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
      rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
        rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht k i j = 𝟙 _ := by
  have : Mono (d i j) := rawGluingInclusion_mono 𝒰 A V d y ℓ hV i j
  have : Mono (d i k) := rawGluingInclusion_mono 𝒰 A V d y ℓ hV i k
  let K := gluingRecoveryFunctor ψ
  apply (cancel_mono (pullback.fst (d i j) (d i k))).mp
  apply hinj (rawGluingTriple 𝒰 A V d i j k) i j
  apply (cancel_mono (K.map (d i j) ≫ h i)).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [rawGluingTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec k i j,
    rawGluingTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec j k i,
    rawGluingTripleTransition_chartMap 𝒰 A V d y ℓ hV t ht ψ h hrec i j k,
    K.map_id, Category.id_comp]

/-- Actual cartesian overlaps and recovered transitions produce scheme gluing
data, with the diagonal and triple cocycle laws proved by injectivity into the actual overlaps. -/
def finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective : Scheme.GlueData.{u} := by
  let D : CategoryTheory.GlueData (Over B) :=
    { J := 𝒰.I₀
      U := A
      V := V
      f := d
      f_mono := rawGluingInclusion_mono 𝒰 A V d y ℓ hV
      f_id := rawGluingInclusion_isIso 𝒰 A V d y ℓ hV
      t := t
      t_id := rawGluingTransition_id 𝒰 A V d y ℓ hV t ψ h hrec hinj
      t' := rawGluingTripleTransition 𝒰 A V d y ℓ hV t ht
      t_fac := rawGluingTripleTransition_fac 𝒰 A V d y ℓ hV t ht
      cocycle := rawGluingTripleTransition_cocycle 𝒰 A V d y ℓ hV t ht ψ h hrec hinj }
  exact
    { toGlueData := D.mapGlueData (Over.forget B)
      f_open := rawGluingInclusion_open 𝒰 A V d y ℓ hV }

/-- The gluing data retain the actual local model objects. -/
theorem finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective_U (i : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
      𝒰 A V d y ℓ hV t ht ψ h hrec hinj).U i =
      (A i).left := rfl

/-- The gluing data retain the actual overlap inclusions. -/
theorem finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective_f (i j : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
      𝒰 A V d y ℓ hV t ht ψ h hrec hinj).f i j =
      (d i j).left := rfl

/-- The gluing data retain the actually descended transition maps. -/
theorem finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective_t (i j : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
      𝒰 A V d y ℓ hV t ht ψ h hrec hinj).t i j =
      (t i j).left := rfl

/-- Recovered transitions glue the actual finite étale local models to an
actual finite étale scheme over the covered base. -/
theorem exists_finiteEtale_fromRecoveredTransitionsOfOverlapInjective
    [∀ i : 𝒰.I₀, IsFiniteEtale (y i)] :
    ∃ q : (finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
      𝒰 A V d y ℓ hV t ht ψ h hrec hinj).glued ⟶ S,
      IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
        IsPullback (y i)
          ((finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
            𝒰 A V d y ℓ hV t ht ψ h hrec hinj).ι i)
          (𝒰.f i) q := by
  let D := finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective
    𝒰 A V d y ℓ hV t ht ψ h hrec hinj
  have : ∀ i : D.J, IsOpenImmersion (𝒰.f i) :=
    fun i => inferInstanceAs (IsOpenImmersion (𝒰.f (show 𝒰.I₀ from i)))
  have : ∀ i : D.J, IsFiniteEtale (show D.U i ⟶ 𝒰.X i from y i) :=
    fun i => inferInstanceAs (IsFiniteEtale (y (show 𝒰.I₀ from i)))
  exact exists_finiteEtale_gluedToBase D S 𝒰.X 𝒰.f 𝒰.exists_eq y ℓ hV ht

variable [Flat ψ] [Surjective ψ]

/-- Actual cartesian overlaps and recovered transitions produce scheme gluing
data, with the diagonal and triple cocycle laws proved by faithful pullback. -/
abbrev finiteStageGlueDataOfRecoveredTransitions : Scheme.GlueData.{u} :=
  finiteStageGlueDataOfRecoveredTransitionsOfOverlapInjective 𝒰 A V d y ℓ hV t ht ψ h hrec
    (fun T i j => (gluingRecoveryFunctor ψ).map_injective (X := T) (Y := V (i, j)))

/-- The gluing data retain the actual local model objects. -/
theorem finiteStageGlueDataOfRecoveredTransitions_U (i : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitions 𝒰 A V d y ℓ hV t ht ψ h hrec).U i =
      (A i).left := rfl

/-- The gluing data retain the actual overlap inclusions. -/
theorem finiteStageGlueDataOfRecoveredTransitions_f (i j : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitions 𝒰 A V d y ℓ hV t ht ψ h hrec).f i j =
      (d i j).left := rfl

/-- The gluing data retain the actually descended transition maps. -/
theorem finiteStageGlueDataOfRecoveredTransitions_t (i j : 𝒰.I₀) :
    (finiteStageGlueDataOfRecoveredTransitions 𝒰 A V d y ℓ hV t ht ψ h hrec).t i j =
      (t i j).left := rfl

/-- Recovered transitions glue the actual finite étale local models to an
actual finite étale scheme over the covered base. -/
theorem exists_finiteEtale_fromRecoveredTransitions [∀ i : 𝒰.I₀, IsFiniteEtale (y i)] :
    ∃ q : (finiteStageGlueDataOfRecoveredTransitions 𝒰 A V d y ℓ hV t ht ψ h hrec).glued ⟶ S,
      IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
        IsPullback (y i)
          ((finiteStageGlueDataOfRecoveredTransitions 𝒰 A V d y ℓ hV t ht ψ h hrec).ι i)
          (𝒰.f i) q := by
  exact exists_finiteEtale_fromRecoveredTransitionsOfOverlapInjective
    𝒰 A V d y ℓ hV t ht ψ h hrec
      (fun T i j => (gluingRecoveryFunctor ψ).map_injective (X := T) (Y := V (i, j)))

end EtaleFundamentalGroups
