/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperIdempotentSectionLift
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteSplitIdempotentSurjectivity
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Restriction to a split closed-fibre section algebra

For a proper scheme over a Noetherian local base, each closed-fibre
idempotent is lifted by the proper cohomology theorem. If the closed-fibre
section algebra is split, these lifts and lifts of residue coefficients
give surjectivity of the actual restriction map on sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Proper idempotent lifting supplies surjectivity on sections when the
actual closed-fibre algebra is finite split. -/
theorem surjective_closedFiber_appTop_of_isProper_of_isFiniteSplit
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    let q : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
    let : Algebra (IsLocalRing.ResidueField A) Γ(pullback f q, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField A))).inv ≫
        (pullback.snd f q).appTop).hom.toAlgebra
    Algebra.IsFiniteSplit (IsLocalRing.ResidueField A) Γ(pullback f q, ⊤) →
      Function.Surjective (pullback.fst f q).appTop := by
  intro q hκ hSplit
  let : Algebra A Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra A Γ(pullback f q, ⊤) :=
    Algebra.compHom Γ(pullback f q, ⊤) (IsLocalRing.residue A)
  have : IsScalarTower A (IsLocalRing.ResidueField A) Γ(pullback f q, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let ψ : Γ(X, ⊤) →ₐ[A] Γ(pullback f q, ⊤) :=
    { toRingHom := (pullback.fst f q).appTop.hom
      commutes' := fun a => by
        change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop) ≫
          (pullback.fst f q).appTop) a =
          (CommRingCat.ofHom (IsLocalRing.residue A) ≫
            (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField A))).inv ≫
              (pullback.snd f q).appTop) a
        congr 2
        rw [Category.assoc, ← Scheme.Hom.comp_appTop, pullback.condition,
          Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] }
  apply Algebra.surjective_of_isFiniteSplit_of_idempotents_mem_range
    ψ IsLocalRing.residue_surjective
  intro e he
  obtain ⟨a, ha⟩ := exists_appTop_eq_of_isProper_of_isIdempotentElem
    f (IsLocalRing.maximalIdeal A) e he
  exact ⟨a, ha⟩

end AlgebraicGeometry
