/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.RegularLocal.ExactRootRightComparison
import EtaleFundamentalGroups.Kummer.SelectedRoot.Intermediate.ExponentUnit

/-!
# Domain sources for literal one-root comparisons

These two source theorems establish the domain inputs used by literal
one-root comparisons: first for the one-stage iterated radical itself, then
after passing to the explicit finite-etale residue lift.  Chosen-factor and
generic-fibre consequences are assembled by their dedicated downstream
leaves.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The one-stage iterated radical over a regular parameter is a domain.
The proof uses its literal `AdjoinRoot` presentation. -/
theorem oneIteratedRadicalIsDomain_of_regularPair
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (y z : A) (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ y
    IsDomain (iteratedRadical A 1 n a) := by
  dsimp only
  let : IsDomain A := isDomain_of_regularSystem [y, z] hreg hgen
  have hymax : y ∈ IsLocalRing.maximalIdeal A := by
    rw [← hgen]
    exact Ideal.subset_span (by simp)
  let Rn := AdjoinRoot (X ^ N - C y)
  let : IsLocalRing Rn :=
    isLocalRing_adjoinRoot_X_pow_sub_C hN hymax
  let : IsDomain Rn := by
    simpa only [Rn] using
      (localRootCover_regularSystem_geometry hN hreg hgen).2.1
  let e := oneIteratedRadicalAlgEquiv A N y
  exact e.toMulEquiv.isDomain Rn

/-- After finite-etale residue lifting, adjoining a root of the first regular
parameter still produces a domain. -/
theorem finiteEtaleResidueLift_pair_adjoinRoot_isDomain_of_regularPair
    {A l : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    (y z : A)
    (hreg : RingTheory.Sequence.IsRegular A [y, z])
    (hgen : Ideal.ofList [y, z] = IsLocalRing.maximalIdeal A)
    (N : ℕ) (hN : 0 < N) :
    let C₁ := FiniteEtaleResidueLift A l
    letI : IsDomain C₁ :=
      finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
    IsDomain
      (AdjoinRoot (X ^ N - C (algebraMap A C₁ y))) := by
  dsimp only
  let C₁ := FiniteEtaleResidueLift A l
  let yC := algebraMap A C₁ y
  let zC := algebraMap A C₁ z
  let : IsLocalRing C₁ := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C₁ := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.Etale A C₁ := etale_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C₁ := Algebra.IsIntegral.of_finite A C₁
  let : FaithfulSMul A C₁ := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C₁) :=
    Algebra.IsIntegral.isLocalHom A C₁
  let : IsNoetherianRing C₁ := IsNoetherianRing.of_finite A C₁
  let : IsDomain C₁ :=
    finiteEtaleResidueLiftIsDomain_of_regularSystem hreg hgen
  have hgeometry :=
    finiteEtale_regularSystem_geometry
      (A := A) (C := C₁) (ps := [y, z]) hreg hgen
  have hregC : RingTheory.Sequence.IsRegular C₁ [yC, zC] := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometry.2.2.1
  have hgenC : Ideal.ofList [yC, zC] = IsLocalRing.maximalIdeal C₁ := by
    simpa only [List.map_cons, List.map_nil, yC, zC] using
      hgeometry.2.2.2.1
  have hymax : yC ∈ IsLocalRing.maximalIdeal C₁ := by
    rw [← hgenC]
    exact Ideal.subset_span (by simp)
  let : IsLocalRing (AdjoinRoot (X ^ N - C yC)) :=
    isLocalRing_adjoinRoot_X_pow_sub_C hN hymax
  exact (localRootCover_regularSystem_geometry hN hregC hgenC).2.1

end EtaleFundamentalGroups.Kummer

end
