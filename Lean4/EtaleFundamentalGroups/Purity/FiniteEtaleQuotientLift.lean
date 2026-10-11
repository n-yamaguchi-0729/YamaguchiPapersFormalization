/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.FiniteEtaleQuotientProductLift
import EtaleFundamentalGroups.Purity.IdempotentFactorProduct
import EtaleFundamentalGroups.Purity.Local.FiniteEtaleQuotientLift
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite étale algebras over quotients of complete local rings

A finite étale algebra over a quotient of a complete Noetherian local ring
splits into finitely many local factors.  Lifting those factors separately and
taking their product gives a finite étale algebra over the original ring whose
base change is the given algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing
open scoped TensorProduct

universe u

/-- A finite family of finite étale lifts can be assembled into a single lift
by taking the product of the lifted algebras. -/
theorem exists_finiteEtale_product_lift
    {R B J : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Finite J]
    (D : J → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra B (D j)]
    (hlift : ∀ j, ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (B ⊗[R] C ≃ₐ[B] D j)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (B ⊗[R] C ≃ₐ[B] ∀ j, D j) := by
  classical
  let := Fintype.ofFinite J
  choose C hCcomm hCalgebra hCfinite hCetale hCequiv using hlift
  let (j : J) : CommRing (C j) := hCcomm j
  let (j : J) : Algebra R (C j) := hCalgebra j
  let (j : J) : Module.Finite R (C j) := hCfinite j
  let (j : J) : Algebra.Etale R (C j) := hCetale j
  refine ⟨∀ j, C j, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight R B B C).trans
    (AlgEquiv.piCongrRight fun j ↦ Classical.choice (hCequiv j))

/-- Every finite étale algebra over a quotient of a complete Noetherian
local ring is obtained by base change from a finite étale algebra over the
original ring. -/
theorem exists_finiteEtale_lift_of_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (I : Ideal R) (hI : I ≤ maximalIdeal R)
    {D : Type u} [CommRing D] [Algebra (R ⧸ I) D]
    [Module.Finite (R ⧸ I) D] [Algebra.Etale (R ⧸ I) D] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Module.Finite R C) (_ : Algebra.Etale R C),
      Nonempty (((R ⧸ I) ⊗[R] C) ≃ₐ[R ⧸ I] D) := by
  classical
  let B := R ⧸ I
  have hIne : I ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  let : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing B :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmaximal :
      (maximalIdeal R).map (algebraMap R B) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (maximalIdeal B) B := by
    rw [← hmaximal]
    exact isAdicComplete_map_maximalIdeal_quotient I
  obtain ⟨J, hJfin, hJdec, A, hAfield, hAalg, E, e, he, hmap,
      hfactors⟩ :=
    exists_closedFiber_fieldFactors_with_finiteEtale_localFactors
      (B := B) (D := D)
  let : Fintype J := hJfin
  let : DecidableEq J := hJdec
  have hlift (j : J) :
      ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C)
        (_ : Module.Finite R C) (_ : Algebra.Etale R C),
        Nonempty (B ⊗[R] C ≃ₐ[B] D ⧸ Ideal.span {1 - e j}) := by
    let : Module.Finite B (D ⧸ Ideal.span {1 - e j}) :=
      (hfactors j).1
    let : Algebra.Etale B (D ⧸ Ideal.span {1 - e j}) :=
      (hfactors j).2.1
    let : IsLocalRing (D ⧸ Ideal.span {1 - e j}) :=
      (hfactors j).2.2
    exact exists_finiteEtaleLocal_lift_of_quotient I hI
  obtain ⟨C, hCcomm, hCalgebra, hCfinite, hCetale, hCbase⟩ :=
    exists_finiteEtale_product_lift
      (R := R) (B := B)
      (fun j ↦ D ⧸ Ideal.span {1 - e j}) hlift
  exact ⟨C, hCcomm, hCalgebra, hCfinite, hCetale,
    hCbase.map fun φ ↦ φ.trans (he.quotientPiAlgEquiv (B := B)).symm⟩

end EtaleFundamentalGroups

end
