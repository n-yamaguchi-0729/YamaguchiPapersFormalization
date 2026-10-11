/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import EtaleFundamentalGroups.FiniteEtale.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The actual adic tower of a finite étale closed-fibre cover

Starting from a finite étale cover of `X × Spec (A / I)`, successive thickening
invariance constructs covers of `X × Spec (A / I^(n+1))`. The transition
morphisms are obtained from the actual Limits.pullback recovery isomorphisms, and
their squares are proved cartesian.

This supplies the finite-cover system used in the proof of Stacks 0A48/0GS2
before applying 09ZT. It does not construct a cover of `X`; the effectivity
step of Grothendieck existence is a separate, still required theorem.

Mathematical sources:
https://stacks.math.columbia.edu/tag/0A48
https://stacks.math.columbia.edu/tag/0GS2
https://stacks.math.columbia.edu/tag/09ZT
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

local instance finiteEtaleInfStableUnderBaseChangeAdicTower :
    MorphismProperty.IsStableUnderBaseChange
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) :=
  MorphismProperty.IsStableUnderBaseChange.inf

variable {A : Type u} [CommRing A]

/-- Positive ideal powers, with the zeroth entry literally the given ideal. -/
def levelIdeal (I : Ideal A) : ℕ → Ideal A
  | 0 => I
  | n + 1 => levelIdeal I n * I

theorem levelIdeal_eq_pow (I : Ideal A) (n : ℕ) : levelIdeal I n = I ^ (n + 1) := by
  induction n with
  | zero => exact (pow_one I).symm
  | succ n ih =>
      change levelIdeal I n * I = I ^ (n + 1 + 1)
      rw [ih, pow_succ I (n + 1)]

theorem levelIdeal_succ_le (I : Ideal A) (n : ℕ) :
    levelIdeal I (n + 1) ≤ levelIdeal I n :=
  Ideal.mul_le_left

/-- The actual quotient spectrum at the `n+1`-st ideal power. -/
def base (I : Ideal A) (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (A ⧸ levelIdeal I n))

/-- The actual closed immersion from an ideal-power quotient spectrum. -/
def baseInclusion (I : Ideal A) (n : ℕ) : base I n ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))

/-- The quotient map induces the successive nilpotent thickening. -/
def baseTransition (I : Ideal A) (n : ℕ) : base I n ⟶ base I (n + 1) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (levelIdeal_succ_le I n)))

theorem baseTransition_comp (I : Ideal A) (n : ℕ) :
    baseTransition I n ≫ baseInclusion I (n + 1) = baseInclusion I n := by
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (levelIdeal_succ_le I n))) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I (n + 1)))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

theorem baseTransition_isClosedImmersion (I : Ideal A) (n : ℕ) :
    IsClosedImmersion (baseTransition I n) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.factor (levelIdeal_succ_le I n)))
    (Ideal.Quotient.factor_surjective (levelIdeal_succ_le I n))

theorem factor_ker_le_nilradical (I : Ideal A) (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (levelIdeal_succ_le I n)) ≤
      nilradical (A ⧸ levelIdeal I (n + 1)) := by
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have ha : a ∈ levelIdeal I n := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hz
  have haI : a ∈ I := by
    rw [levelIdeal_eq_pow] at ha
    exact Ideal.pow_le_self (Nat.succ_ne_zero n) ha
  apply mem_nilradical.mpr
  refine ⟨n + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, levelIdeal_eq_pow]
  exact Ideal.pow_mem_pow haI (n + 2)

theorem baseTransition_surjective (I : Ideal A) (n : ℕ) :
    Surjective (baseTransition I n) := by
  let q : (A ⧸ levelIdeal I (n + 1)) →+* (A ⧸ levelIdeal I n) :=
    Ideal.Quotient.factor (levelIdeal_succ_le I n)
  have hq : Function.Surjective q :=
    Ideal.Quotient.factor_surjective (levelIdeal_succ_le I n)
  have hDense : DenseRange (PrimeSpectrum.comap q) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical q).mpr
      (factor_ker_le_nilradical I n)
  have hClosed : IsClosed (Set.range (PrimeSpectrum.comap q)) :=
    PrimeSpectrum.isClosed_range_comap_of_surjective (A ⧸ levelIdeal I n) q hq
  constructor
  change Function.Surjective (PrimeSpectrum.comap q)
  apply Set.range_eq_univ.mp
  rw [← hClosed.closure_eq, hDense.closure_range]

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)

/-- The actual base change of `X` at level `n+1`. -/
abbrev level (n : ℕ) : Scheme.{u} := Limits.pullback f (baseInclusion I n)

/-- The morphism between the actual successive base changes. -/
def transition (n : ℕ) : level f I n ⟶ level f I (n + 1) :=
  Limits.pullback.lift (Limits.pullback.fst f (baseInclusion I n))
    (Limits.pullback.snd f (baseInclusion I n) ≫ baseTransition I n)
    (by
      calc
        Limits.pullback.fst f (baseInclusion I n) ≫ f =
            Limits.pullback.snd f (baseInclusion I n) ≫ baseInclusion I n :=
          Limits.pullback.condition (f := f) (g := baseInclusion I n)
        _ = Limits.pullback.snd f (baseInclusion I n) ≫
            (baseTransition I n ≫ baseInclusion I (n + 1)) :=
          congrArg
            (fun g : base I n ⟶ Spec (CommRingCat.of A) =>
              Limits.pullback.snd f (baseInclusion I n) ≫ g)
            (baseTransition_comp I n).symm
        _ = (Limits.pullback.snd f (baseInclusion I n) ≫ baseTransition I n) ≫
            baseInclusion I (n + 1) :=
          (Category.assoc _ _ _).symm)

theorem transition_fst (n : ℕ) :
    transition f I n ≫ Limits.pullback.fst f (baseInclusion I (n + 1)) =
      Limits.pullback.fst f (baseInclusion I n) :=
  Limits.pullback.lift_fst _ _ _

theorem transition_snd (n : ℕ) :
    transition f I n ≫ Limits.pullback.snd f (baseInclusion I (n + 1)) =
      Limits.pullback.snd f (baseInclusion I n) ≫ baseTransition I n :=
  Limits.pullback.lift_snd _ _ _

theorem transition_isPullback (n : ℕ) :
    IsPullback (transition f I n) (Limits.pullback.snd f (baseInclusion I n))
      (Limits.pullback.snd f (baseInclusion I (n + 1))) (baseTransition I n) := by
  apply IsPullback.of_right (p := transition_snd f I n)
    (t := IsPullback.of_hasPullback f (baseInclusion I (n + 1)))
  rw [transition_fst, baseTransition_comp]
  exact IsPullback.of_hasPullback f (baseInclusion I n)

theorem transition_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (transition f I n) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (transition_isPullback f I n).flip (baseTransition_isClosedImmersion I n)

theorem transition_surjective (n : ℕ) :
    Surjective (transition f I n) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (transition_isPullback f I n).flip (baseTransition_surjective I n)

section LiftedCover

variable (V : MorphismProperty.Over
  ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- The covers are constructed by recursion from the supplied closed-fibre cover. -/
def cover (n : ℕ) :
    MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I n) :=
  Nat.rec (motive := fun k : ℕ =>
    MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I k)) V
    (fun k W =>
      let : IsClosedImmersion (transition f I k) := transition_isClosedImmersion f I k
      let : Surjective (transition f I k) := transition_surjective f I k
      let G :
          MorphismProperty.Over
            ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I (k + 1)) ⥤
          MorphismProperty.Over
            ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I k) :=
        MorphismProperty.Over.pullback
          ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (transition f I k)
      let : G.EssSurj := pullback_essSurj_of_surjective_closedImmersion (transition f I k)
      G.objPreimage W) n

theorem cover_zero : cover f I V 0 = V := rfl

/-- The chosen lifts recover the previous level under the literal pullback functor. -/
def coverRecoveryIso (n : ℕ) :
    (MorphismProperty.Over.pullback
          ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (transition f I n)).obj
        (cover f I V (n + 1)) ≅
      cover f I V n := by
  let : IsClosedImmersion (transition f I n) := transition_isClosedImmersion f I n
  let : Surjective (transition f I n) := transition_surjective f I n
  let G :
      MorphismProperty.Over
        ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I (n + 1)) ⥤
      MorphismProperty.Over
        ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I n) :=
    MorphismProperty.Over.pullback
          ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (transition f I n)
  let : G.EssSurj := pullback_essSurj_of_surjective_closedImmersion (transition f I n)
  exact G.objObjPreimageIso (cover f I V n)

/-- The recovery isomorphism on the actual underlying pullback schemes. -/
def underlyingRecoveryIso (n : ℕ) :
    Limits.pullback (cover f I V (n + 1)).hom (transition f I n) ≅ (cover f I V n).left :=
  (MorphismProperty.Over.forget
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I n) ⋙
    Over.forget (level f I n)).mapIso (coverRecoveryIso f I V n)

theorem recovery_inv_snd (n : ℕ) :
    (underlyingRecoveryIso f I V n).inv ≫
        Limits.pullback.snd (cover f I V (n + 1)).hom (transition f I n) =
      (cover f I V n).hom :=
  MorphismProperty.Over.w (coverRecoveryIso f I V n).inv

/-- The actual scheme morphism joining consecutive lifted covers. -/
def coverTransition (n : ℕ) :
    (cover f I V n).left ⟶ (cover f I V (n + 1)).left :=
  (underlyingRecoveryIso f I V n).inv ≫
    Limits.pullback.fst (cover f I V (n + 1)).hom (transition f I n)

theorem coverTransition_comm (n : ℕ) :
    coverTransition f I V n ≫ (cover f I V (n + 1)).hom =
      (cover f I V n).hom ≫ transition f I n := by
  change ((underlyingRecoveryIso f I V n).inv ≫
      Limits.pullback.fst (cover f I V (n + 1)).hom (transition f I n)) ≫
      (cover f I V (n + 1)).hom = (cover f I V n).hom ≫ transition f I n
  rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, recovery_inv_snd]

/-- Every successor square in the constructed cover tower is cartesian. -/
theorem coverTransition_isPullback (n : ℕ) :
    IsPullback (coverTransition f I V n) (cover f I V n).hom
      (cover f I V (n + 1)).hom (transition f I n) :=
  IsPullback.of_iso_pullback ⟨coverTransition_comm f I V n⟩
    (underlyingRecoveryIso f I V n).symm rfl (recovery_inv_snd f I V n)

end LiftedCover

/-- For a proper original scheme this is the actual finite-cover input of 09ZT.
No completeness or Noetherian hypothesis is needed to construct the tower itself. -/
theorem exists_proper_finiteEtale_cover_tower [IsProper f]
    (V : MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤
      (Limits.pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ W : (n : ℕ) → MorphismProperty.Over
      ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I n),
      ∃ r : (n : ℕ) → (W n).left ⟶ (W (n + 1)).left,
        W 0 = V ∧
        (∀ n : ℕ, IsPullback (r n) (W n).hom (W (n + 1)).hom (transition f I n)) ∧
        (∀ n : ℕ, IsProper ((W n).hom ≫ Limits.pullback.snd f (baseInclusion I n))) := by
  refine ⟨cover f I V, coverTransition f I V, rfl,
    coverTransition_isPullback f I V, ?_⟩
  intro n
  have hFinite : IsFinite (cover f I V n).hom := (cover f I V n).prop.1
  have hProperCover : IsProper (cover f I V n).hom := inferInstance
  have hProperLevel : IsProper (Limits.pullback.snd f (baseInclusion I n)) :=
    inferInstance
  exact MorphismProperty.comp_mem (@IsProper : MorphismProperty Scheme.{u})
    (cover f I V n).hom (Limits.pullback.snd f (baseInclusion I n))
    hProperCover hProperLevel

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
