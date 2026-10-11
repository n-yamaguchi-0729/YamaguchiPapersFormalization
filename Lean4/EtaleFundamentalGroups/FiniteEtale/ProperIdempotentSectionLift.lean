/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Affine.HomeomorphismIdempotentSections
import SchemeTheory.Morphisms.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proper idempotent-section lifting over a Noetherian affine base

An idempotent on a closed fibre lifts through every infinitesimal
thickening because the thickenings have the same underlying space.
The proper-cohomology stabilization theorem then produces a global
section with that restriction. The global section need not be idempotent.

This is the Noetherian supplier for Stacks Project Tag 0G7X. Extending it
to an arbitrary finitely presented proper family still requires descending
the family and the finite idempotent relation to a Noetherian model.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An idempotent section on any closed fibre of a proper morphism over a
Noetherian affine base is the restriction of a global section. -/
theorem exists_appTop_eq_of_isProper_of_isIdempotentElem
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A) :
    ∀ e : Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))), ⊤),
      IsIdempotentElem e → ∃ a : Γ(X, ⊤),
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).appTop a = e := by
  let q (n : ℕ) : Spec (CommRingCat.of (A ⧸ I ^ n)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n)))
  let j (n : ℕ) : pullback f (q n) ⟶ X := pullback.fst f (q n)
  have hClosed (n : ℕ) : IsClosedImmersion (j n) := by
    have hQuotient : IsClosedImmersion (q n) :=
      IsClosedImmersion.spec_of_surjective
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))) Ideal.Quotient.mk_surjective
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback f (q n)).flip hQuotient
  have hRange (n : ℕ) (hn : n ≠ 0) :
      Set.range (j n) = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    change Set.range (pullback.fst f (q n)) = _
    rw [Scheme.Pullback.range_fst]
    have hq : Set.range (q n) = PrimeSpectrum.zeroLocus (I : Set A) := by
      change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n))) = _
      rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow I hn]
    rw [hq]
  have hLift : ∀ e : Γ(pullback f (q 1), ⊤),
      IsIdempotentElem e → ∃ a : Γ(X, ⊤), (j 1).appTop a = e := by
    intro e he
    obtain ⟨c, hc⟩ :=
      exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper I f 1
    let τ : pullback f (q 1) ⟶ pullback f (q (1 + c)) :=
      pullback.map f (q 1) f (q (1 + c)) (𝟙 X)
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right 1 c)))))
        (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
        (by
          dsimp only [q]
          rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            Ideal.Quotient.factor_comp_mk])
    have hτ : τ ≫ j (1 + c) = j 1 := by
      dsimp only [τ, j]
      rw [pullback.lift_fst, Category.comp_id]
    have : IsClosedImmersion (τ ≫ j (1 + c)) := hτ.symm ▸ hClosed 1
    have : IsClosedImmersion τ :=
      IsClosedImmersion.of_comp_isClosedImmersion τ (j (1 + c))
    have hSurj : Function.Surjective τ := by
      intro y
      have hy : j (1 + c) y ∈ Set.range (j 1) := by
        rw [hRange 1 one_ne_zero,
          ← hRange (1 + c) (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 c)).ne']
        exact ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := hy
      refine ⟨x, (j (1 + c)).isEmbedding.injective ?_⟩
      change (τ ≫ j (1 + c)) x = j (1 + c) y
      rw [hτ]
      exact hx
    have hHomeomorph : IsHomeomorph τ :=
      isHomeomorph_iff_isEmbedding_surjective.mpr ⟨τ.isEmbedding, hSurj⟩
    obtain ⟨b, hb⟩ :=
      τ.exists_appTop_eq_of_isHomeomorph_of_isIdempotentElem hHomeomorph e he
    obtain ⟨a, ha⟩ := hc b
    have ha' : τ.appTop b = (j 1).appTop a := ha
    exact ⟨a, ha'.symm.trans hb⟩
  let liftProperty (J : Ideal A) : Prop :=
    ∀ e : Γ(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))), ⊤),
      IsIdempotentElem e → ∃ a : Γ(X, ⊤),
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).appTop a = e
  have hLift' : liftProperty (I ^ 1) := hLift
  exact (congrArg liftProperty (pow_one I)).mp hLift'

end AlgebraicGeometry
