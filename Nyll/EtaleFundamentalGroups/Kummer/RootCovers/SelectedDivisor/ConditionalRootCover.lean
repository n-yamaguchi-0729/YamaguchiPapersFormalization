/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Conditional
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.SelectedDivisor.RootCover

/-!
# A selected divisor under a height-two conditional root cover

At a height-two point, after placing the sole possible non-selected boundary
branch first, all remaining conditional root stages have exponent one.  This
file removes those degree-one stages by an explicit algebra equivalence and
transports the selected-divisor geometry from the one-root cover.  When no
non-selected branch passes through the point, every stage has exponent one;
the resulting tower is identified with the base before transporting the same
geometry.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

/-- If every iterated radical stage after the first has exponent one, the
whole tower is canonically equivalent to its first root-adjunction. -/
def iteratedRadicalTailOneAlgEquiv
    {R : Type u} [CommRing R] :
    {r : ℕ} → (n : Fin (r + 1) → ℕ) → (a : Fin (r + 1) → R) →
      (∀ i : Fin r, n i.succ = 1) →
      iteratedRadical R (r + 1) n a ≃ₐ[R]
        iteratedRadical R 1 (fun _ ↦ n 0) (fun _ ↦ a 0)
  | 0, n, a, _ => by
      exact AlgEquiv.refl
  | r + 1, n, a, htail => by
      let nInit : Fin (r + 1) → ℕ := Fin.init n
      let aInit : Fin (r + 1) → R := Fin.init a
      let T : CommAlgCat R := iteratedRadical R (r + 1) nInit aInit
      have hlast : n (Fin.last (r + 1)) = 1 := by
        simpa using htail (Fin.last r)
      have htailInit : ∀ i : Fin r, nInit i.succ = 1 := by
        intro i
        change n i.succ.castSucc = 1
        convert htail i.castSucc using 1
        apply congrArg n
        ext
        rfl
      let c : T := algebraMap R T (a (Fin.last (r + 1)))
      let f : T[X] := X ^ n (Fin.last (r + 1)) - C c
      have hf : f = X ^ 1 - C c := by simp [f, hlast]
      let eT : AdjoinRoot f ≃ₐ[T] T :=
        (AdjoinRoot.algEquivOfEq T f (X ^ 1 - C c) hf).trans
          (adjoinRootOneAlgEquiv c)
      let eR : AdjoinRoot f ≃ₐ[R] T := eT.restrictScalars R
      let eLast : iteratedRadical R (r + 2) n a ≃ₐ[R] T := eR
      exact eLast.trans
        (iteratedRadicalTailOneAlgEquiv nInit aInit htailInit)

/-- If every stage of an iterated radical has exponent one, the whole tower
is canonically equivalent to the base ring. -/
def iteratedRadicalAllOneAlgEquiv
    {R : Type u} [CommRing R] :
    {r : ℕ} → (n : Fin r → ℕ) → (a : Fin r → R) →
      (∀ i, n i = 1) → iteratedRadical R r n a ≃ₐ[R] R
  | 0, _, _, _ => AlgEquiv.refl
  | r + 1, n, a, hall => by
      let eTail : iteratedRadical R (r + 1) n a ≃ₐ[R]
          iteratedRadical R 1 (fun _ ↦ n 0) (fun _ ↦ a 0) :=
        iteratedRadicalTailOneAlgEquiv n a (fun i ↦ hall i.succ)
      let eHead :
          iteratedRadical R 1 (fun _ ↦ n 0) (fun _ ↦ a 0) ≃ₐ[R] R := by
        let c : R := algebraMap R R (a 0)
        let f : R[X] := X ^ n 0 - C c
        have hf : f = X ^ 1 - C (a 0) := by
          simp [f, c, hall 0]
        change AdjoinRoot f ≃ₐ[R] R
        exact (AdjoinRoot.algEquivOfEq R f (X ^ 1 - C (a 0)) hf).trans
          (adjoinRootOneAlgEquiv (a 0))
      exact eTail.trans eHead

private theorem selectedDivisorGeometry_of_algEquiv
    {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    (e : B ≃ₐ[R] C) {y : R}
    (hC : IsRegularLocalRing C ∧ IsDomain C ∧
      Prime (algebraMap R C y) ∧
      IsDomain (C ⧸ Ideal.span ({algebraMap R C y} : Set C)) ∧
      IsRegularLocalRing
        (C ⧸ Ideal.span ({algebraMap R C y} : Set C))) :
    IsRegularLocalRing B ∧ IsDomain B ∧
      Prime (algebraMap R B y) ∧
      IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
      IsRegularLocalRing
        (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
  rcases hC with ⟨hregC, hdomainC, hyCPrime, hdomainCQ, hregCQ⟩
  let : IsRegularLocalRing C := hregC
  let : IsDomain C := hdomainC
  let IC : Ideal C := Ideal.span ({algebraMap R C y} : Set C)
  let IB : Ideal B := Ideal.span ({algebraMap R B y} : Set B)
  have hIC : IC = IB.map (e : B →+* C) := by
    simp [IC, IB, Ideal.map_span]
  let eQ : (B ⧸ IB) ≃+* (C ⧸ IC) :=
    Ideal.quotientEquiv IB IC e.toRingEquiv hIC
  have hdomainCQ' : IsDomain (C ⧸ IC) := by
    simpa [IC] using hdomainCQ
  let : IsDomain (C ⧸ IC) := hdomainCQ'
  have hregCQ' : IsRegularLocalRing (C ⧸ IC) := by
    simpa [IC] using hregCQ
  let : IsRegularLocalRing (C ⧸ IC) := hregCQ'
  have hregB : IsRegularLocalRing B :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  have hdomainB : IsDomain B := e.toMulEquiv.isDomain C
  have hdomainBQ : IsDomain (B ⧸ IB) :=
    eQ.toMulEquiv.isDomain (C ⧸ IC)
  let : IsDomain (B ⧸ IB) := hdomainBQ
  have hIBprime : IB.IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime IB).mp inferInstance
  have hyBNe : algebraMap R B y ≠ 0 := by
    intro hyzero
    apply hyCPrime.ne_zero
    rw [← e.commutes y, hyzero, map_zero]
  have hyBPrime : Prime (algebraMap R B y) := by
    apply (Ideal.span_singleton_prime hyBNe).mp
    exact hIBprime
  have hregBQ : IsRegularLocalRing (B ⧸ IB) :=
    IsRegularLocalRing.of_ringEquiv eQ.symm
  simpa [IB] using
    (show IsRegularLocalRing B ∧ IsDomain B ∧
        Prime (algebraMap R B y) ∧ IsDomain (B ⧸ IB) ∧
        IsRegularLocalRing (B ⧸ IB) from
      ⟨hregB, hdomainB, hyBPrime, hdomainBQ, hregBQ⟩)

/-- If every stage of a conditional root cover has exponent one, a selected
member of a regular parameter pair retains its prime regular-divisor
geometry.  No radicand is required to lie in the maximal ideal: the entire
root tower is first identified with the base ring. -/
theorem allOneRootCover_selectedDivisor_geometry
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → R)
    (hall : ∀ i, n i = 1) {y z : R}
    (hreg : IsRegular R [y, z])
    (hgen : Ideal.ofList [y, z] = maximalIdeal R) :
    let B := iteratedRadical R r n a
    IsRegularLocalRing B ∧ IsDomain B ∧
      Prime (algebraMap R B y) ∧
      IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
      IsRegularLocalRing
        (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
  dsimp only
  let e : iteratedRadical R r n a ≃ₐ[R] R :=
    iteratedRadicalAllOneAlgEquiv n a hall
  apply selectedDivisorGeometry_of_algEquiv e
  have hregR : IsRegularLocalRing R :=
    isRegularLocalRing_of_regularSystem [y, z] hreg hgen
  have hyPrime : Prime y :=
    prime_of_mem_regularSystem hreg hgen List.mem_cons_self
  have hyQuotient :=
    quotient_geometry_of_mem_regularSystem hreg hgen (p := y) List.mem_cons_self
  simpa using
    (show IsRegularLocalRing R ∧ IsDomain R ∧ Prime y ∧
        IsDomain (R ⧸ Ideal.span ({y} : Set R)) ∧
        IsRegularLocalRing (R ⧸ Ideal.span ({y} : Set R)) from
      ⟨hregR, inferInstance, hyPrime, hyQuotient.1, hyQuotient.2⟩)

/--
Height-two conditional form of `oneRootCover_selectedDivisor_geometry`.
There may be arbitrarily many stages after the unique nontrivial root, but
all of them have exponent one and therefore do not change the algebra.
-/
theorem oneRootWithTrivialTail_selectedDivisor_geometry
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    {r : ℕ} (n : Fin (r + 1) → ℕ) (a : Fin (r + 1) → R)
    (htail : ∀ i : Fin r, n i.succ = 1)
    (hn : 0 < n 0) {y : R}
    (hreg : IsRegular R [a 0, y])
    (hgen : Ideal.ofList [a 0, y] = maximalIdeal R) :
    let B := iteratedRadical R (r + 1) n a
    IsRegularLocalRing B ∧ IsDomain B ∧
      Prime (algebraMap R B y) ∧
      IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
      IsRegularLocalRing
        (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
  dsimp only
  let C := iteratedRadical R 1 (fun _ ↦ n 0) (fun _ ↦ a 0)
  let e : iteratedRadical R (r + 1) n a ≃ₐ[R] C :=
    iteratedRadicalTailOneAlgEquiv n a htail
  apply selectedDivisorGeometry_of_algEquiv e
  exact oneRootCover_selectedDivisor_geometry hn hreg hgen

end EtaleFundamentalGroups.Kummer

end
