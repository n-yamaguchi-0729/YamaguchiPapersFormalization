/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import EtaleFundamentalGroups.GenericTensor.FilteredColimit.AlgEquivDescent
import SchemeTheory.FiniteEtale.Henselian.ChosenFactor.Core

/-!
# Finite-stage descent of a strict-Henselian chosen factor

A finite etale factor with one closed prime becomes the base over a strictly
Henselian filtered colimit.  Finite presentation then descends the resulting
equivalence, together with its inverse equations, to one finite stage of the
pointed system.

The equations in the conclusion use the literal tensor-product cocone maps.
They retain the chosen factor and all of its distinguished coordinates; the
finite-stage factor is not reselected after descent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

local instance underCommRingCatAlgebraChosenFactorDescent
    {R : Type u} [CommRing R]
    (A : Under (CommRingCat.of R)) : Algebra R A :=
  RingHom.toAlgebra A.hom.hom

/-- The strict-Henselian trivialization of a chosen finite etale factor,
written between the two tensor products used by finite-stage descent. -/
noncomputable def strictHenselianChosenFactorTensorAlgEquiv
    {R B S : Type u}
    [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S]
    [Module.Finite R B] [Algebra.Etale R B]
    [HenselianLocalRing S]
    [IsSepClosed (IsLocalRing.ResidueField S)]
    (q : Ideal (S ⊗[R] B)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal S)]
    (hunique : ∀ Q : Ideal (S ⊗[R] B), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal S) → Q = q) :
    (S ⊗[R] B) ≃ₐ[S] (S ⊗[R] R) := by
  letI : Algebra S (S ⊗[R] B) :=
    Algebra.TensorProduct.leftAlgebra
  letI : Module.Finite S (S ⊗[R] B) := inferInstance
  letI : Algebra.Etale S (S ⊗[R] B) := inferInstance
  exact
    (strictHenselianChosenFactorAlgEquiv q hunique).symm.trans
      (Algebra.TensorProduct.rid R S S).symm

/-- A chosen finite etale factor which is uniquely closed over a strictly
Henselian filtered colimit is already trivial at one finite stage.

Both comparison equations are returned.  Thus the descended equivalence and
its inverse recover the exact strict-Henselian equivalence after passage to
the colimit. -/
theorem
    exists_strictHenselianChosenFactor_algEquiv_stage_of_filteredColimit
    {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FinitePresentation R B]
    [Module.Finite R B] [Algebra.Etale R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : CategoryTheory.Functor J (Under (CommRingCat.of R)))
    (c : Cocone F) (hc : IsColimit c)
    [HenselianLocalRing c.pt]
    [IsSepClosed (IsLocalRing.ResidueField c.pt)]
    (q : Ideal (c.pt ⊗[R] B)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal c.pt)]
    (hunique : ∀ Q : Ideal (c.pt ⊗[R] B), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal c.pt) → Q = q) :
    let e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] R) :=
      strictHenselianChosenFactorTensorAlgEquiv q hunique
    ∃ (i : J)
      (eᵢ : (F.obj i ⊗[R] B) ≃ₐ[F.obj i]
        (F.obj i ⊗[R] R)),
      (filteredTensorToColimitAlgHom c i (A := R)).comp
          (eᵢ.toAlgHom.restrictScalars R) =
        (e.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c i (A := B)) ∧
      (filteredTensorToColimitAlgHom c i (A := B)).comp
          (eᵢ.symm.toAlgHom.restrictScalars R) =
        (e.symm.toAlgHom.restrictScalars R).comp
          (filteredTensorToColimitAlgHom c i (A := R)) := by
  dsimp only
  let e : (c.pt ⊗[R] B) ≃ₐ[c.pt] (c.pt ⊗[R] R) :=
    strictHenselianChosenFactorTensorAlgEquiv q hunique
  exact exists_tensorProduct_algEquiv_stage_of_filteredColimit
    (R := R) (B := B) (D := R) F c hc e

/-- In particular, at one finite stage the chosen factor itself is the stage
base.  The preceding theorem remains the coordinate-preserving endpoint;
this corollary is the form consumed by finite-etale neighbourhood arguments. -/
theorem
    exists_strictHenselianChosenFactor_trivial_stage_of_filteredColimit
    {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.FinitePresentation R B]
    [Module.Finite R B] [Algebra.Etale R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : CategoryTheory.Functor J (Under (CommRingCat.of R)))
    (c : Cocone F) (hc : IsColimit c)
    [HenselianLocalRing c.pt]
    [IsSepClosed (IsLocalRing.ResidueField c.pt)]
    (q : Ideal (c.pt ⊗[R] B)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal c.pt)]
    (hunique : ∀ Q : Ideal (c.pt ⊗[R] B), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal c.pt) → Q = q) :
    ∃ (i : J), Nonempty
      ((F.obj i ⊗[R] B) ≃ₐ[F.obj i] F.obj i) := by
  obtain ⟨i, eᵢ, _, _⟩ :=
    exists_strictHenselianChosenFactor_algEquiv_stage_of_filteredColimit
      F c hc q hunique
  exact ⟨i, ⟨eᵢ.trans
    (Algebra.TensorProduct.rid R (F.obj i) (F.obj i))⟩⟩

/-- Noetherian specialization: finiteness of the chosen factor supplies the
finite-presentation hypothesis needed for descent. -/
theorem
    exists_strictHenselianChosenFactor_trivial_stage_of_filteredColimit_of_noetherian
    {R B : Type u} [CommRing R] [CommRing B] [IsNoetherianRing R]
    [Algebra R B] [Module.Finite R B] [Algebra.Etale R B]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : CategoryTheory.Functor J (Under (CommRingCat.of R)))
    (c : Cocone F) (hc : IsColimit c)
    [HenselianLocalRing c.pt]
    [IsSepClosed (IsLocalRing.ResidueField c.pt)]
    (q : Ideal (c.pt ⊗[R] B)) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal c.pt)]
    (hunique : ∀ Q : Ideal (c.pt ⊗[R] B), Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal c.pt) → Q = q) :
    ∃ (i : J), Nonempty
      ((F.obj i ⊗[R] B) ≃ₐ[F.obj i] F.obj i) := by
  let : Module.FinitePresentation R B :=
    Module.finitePresentation_of_finite R B
  let : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_finitePresentation R B
  exact
    exists_strictHenselianChosenFactor_trivial_stage_of_filteredColimit
      F c hc q hunique

end EtaleFundamentalGroups

end
