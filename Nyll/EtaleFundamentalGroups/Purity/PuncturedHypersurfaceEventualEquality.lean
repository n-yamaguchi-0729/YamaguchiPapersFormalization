/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.PuncturedHypersurfaceNeighborhoodExistence
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.NatIso

/-!
# Equality of finite étale morphisms after shrinking a neighbourhood

For a Noetherian local ring and an equation in its maximal ideal, any open
containing the punctured hypersurface has a smaller such neighbourhood on
which equality of finite étale morphisms is detected by the hypersurface.
The smaller neighbourhood is the intersection with the faithful
neighbourhood constructed by deleting the bad minimal components.

The proof compares the actual iterated pullbacks along the resulting
commutative square. The shrinking neighbourhood works simultaneously for
all covers and morphisms on the given open.

This is the eventual-equality assertion needed for faithfulness on germs
in [Stacks Project, Tag 0BLN](https://stacks.math.columbia.edu/tag/0BLN).
No category of germs or categorical colimit is constructed here.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteEtale

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- An open containing the punctured hypersurface admits one smaller open
inside the puncture on which every two finite étale morphisms agreeing on
the hypersurface become equal. The covers and the morphisms are arbitrary
objects and morphisms over the original open `W`.

If `W` is itself contained in the puncture, its hypersurface pullback is
precisely the punctured hypersurface occurring in the neighbourhood system. -/
theorem exists_punctured_hypersurface_neighborhood_restriction_eq
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (f : R) (hf : f ∈ maximalIdeal R)
    (W : (Spec (.of R)).Opens)
    (hWzero : ∀ p : PrimeSpectrum R,
      p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ W) :
    ∃ (V : (Spec (.of R)).Opens) (hVW : V ≤ W),
      V ≤ Scheme.puncturedSpectrumOpen R ∧
      (∀ p : PrimeSpectrum R,
        p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ V) ∧
      ∀ (A B : FiniteEtale W.toScheme) (α β : A ⟶ B),
        (FiniteEtale.pullback (Limits.pullback.fst W.ι
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.span {f})))))).map α =
        (FiniteEtale.pullback (Limits.pullback.fst W.ι
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (Ideal.span {f})))))).map β →
        (FiniteEtale.pullback ((Spec (.of R)).homOfLE hVW)).map α =
          (FiniteEtale.pullback ((Spec (.of R)).homOfLE hVW)).map β := by
  obtain ⟨U, hUpuncture, hUzero, hUfaithful⟩ :=
    exists_punctured_hypersurface_neighborhood_faithful R f hf
  let V : (Spec (.of R)).Opens := W ⊓ U
  have hVW : V ≤ W := inf_le_left
  have hVU : V ≤ U := inf_le_right
  have hVzero : ∀ p : PrimeSpectrum R,
      p ∈ Scheme.puncturedSpectrumOpen R → f ∈ p.asIdeal → p ∈ V := by
    intro p hp hfp
    exact ⟨hWzero p hp hfp, hUzero p hp hfp⟩
  refine ⟨V, hVW, hVU.trans hUpuncture, hVzero, ?_⟩
  intro A B α β hαβ
  let i : Spec (.of (R ⧸ Ideal.span {f})) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
  let j : V.toScheme ⟶ W.toScheme := (Spec (.of R)).homOfLE hVW
  let a : Limits.pullback V.ι i ⟶ V.toScheme := Limits.pullback.fst V.ι i
  let b : Limits.pullback W.ι i ⟶ W.toScheme := Limits.pullback.fst W.ι i
  have hcone : (a ≫ j) ≫ W.ι = Limits.pullback.snd V.ι i ≫ i := by
    change (Limits.pullback.fst V.ι i ≫ (Spec (.of R)).homOfLE hVW) ≫ W.ι =
      Limits.pullback.snd V.ι i ≫ i
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact Limits.pullback.condition
  let k : Limits.pullback V.ι i ⟶ Limits.pullback W.ι i :=
    Limits.pullback.lift (a ≫ j) (Limits.pullback.snd V.ι i) hcone
  have hk : k ≫ b = a ≫ j := Limits.pullback.lift_fst _ _ hcone
  let cV : FiniteEtale.pullback (a ≫ j) ≅
      FiniteEtale.pullback j ⋙ FiniteEtale.pullback a :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      a j (a ≫ j) rfl
  let cW : FiniteEtale.pullback (a ≫ j) ≅
      FiniteEtale.pullback b ⋙ FiniteEtale.pullback k :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      k b (a ≫ j) hk.symm
  let e : FiniteEtale.pullback b ⋙ FiniteEtale.pullback k ≅
      FiniteEtale.pullback j ⋙ FiniteEtale.pullback a := cW.symm ≪≫ cV
  have hiterated : (FiniteEtale.pullback b ⋙ FiniteEtale.pullback k).map α =
      (FiniteEtale.pullback b ⋙ FiniteEtale.pullback k).map β :=
    congrArg (fun t : (FiniteEtale.pullback b).obj A ⟶
        (FiniteEtale.pullback b).obj B ↦ (FiniteEtale.pullback k).map t) hαβ
  have : (FiniteEtale.pullback a).Faithful := hUfaithful V hVU hVzero
  apply (FiniteEtale.pullback a).map_injective
  change (FiniteEtale.pullback j ⋙ FiniteEtale.pullback a).map α =
    (FiniteEtale.pullback j ⋙ FiniteEtale.pullback a).map β
  rw [← NatIso.naturality_1 e α, ← NatIso.naturality_1 e β, hiterated]

end AlgebraicGeometry.FiniteEtale
