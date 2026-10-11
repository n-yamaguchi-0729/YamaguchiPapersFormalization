/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import EtaleFundamentalGroups.Kummer.Laurent.DiagonalRadical
import EtaleFundamentalGroups.Kummer.Radicals.Relative
import EtaleFundamentalGroups.Kummer.Descent.RelativeRadical

/-!
# Formal unramifiedness of a diagonal Laurent radical

The radical presentation of a finite lattice cover is dependent: at each
stage the new radicand is the new Laurent monomial over the preceding radical,
rather than an element of the original coefficient ring.  This file proves
that formal unramifiedness of that presentation forces every Smith exponent
to be a unit in the original coefficient ring.

Coefficient extension for additive monoid algebras is handled by its
canonical pushout square.  Faithful flatness is preserved by this base change,
and formal unramifiedness is reflected by faithfully-flat descent.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- Faithful flatness survives coefficient extension in an additive monoid algebra. -/
private theorem mapRingHom_faithfullyFlat
    {A B : Type u} {M : Type}
    [CommRing A] [CommRing B] [AddCommMonoid M]
    (f : A →+* B) (hf : f.FaithfullyFlat) :
    (AddMonoidAlgebra.mapRingHom M f).FaithfullyFlat := by
  let g := AddMonoidAlgebra.mapRingHom M f
  let : Algebra A B := f.toAlgebra
  let : Algebra (AddMonoidAlgebra A M) (AddMonoidAlgebra B M) :=
    g.toAlgebra
  let : IsScalarTower A B (AddMonoidAlgebra B M) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (AddMonoidAlgebra A M)
      (AddMonoidAlgebra B M) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp [g, RingHom.algebraMap_toAlgebra])
  let : Algebra.IsPushout A (AddMonoidAlgebra A M) B
      (AddMonoidAlgebra B M) :=
    AddMonoidAlgebra.instIsPushout'
  have hf' : (algebraMap A B).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hf
  have hg := RingHom.FaithfullyFlat.isStableUnderBaseChange
    A B (AddMonoidAlgebra A M) (AddMonoidAlgebra B M) hf'
  simpa [g, RingHom.algebraMap_toAlgebra] using hg

/-- Formal unramifiedness of a coefficient extension reflects to the
coefficient map. -/
private theorem formallyUnramified_of_mapRingHom
    {A B : Type u} {M : Type} [CommRing A] [Nontrivial A]
    [CommRing B] [AddCommMonoid M]
    (f : A →+* B)
    (hg : (AddMonoidAlgebra.mapRingHom M f).FormallyUnramified) :
    f.FormallyUnramified := by
  let g := AddMonoidAlgebra.mapRingHom M f
  let : Algebra A B := f.toAlgebra
  let : Algebra (AddMonoidAlgebra A M) (AddMonoidAlgebra B M) :=
    g.toAlgebra
  let : IsScalarTower A B (AddMonoidAlgebra B M) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A (AddMonoidAlgebra A M)
      (AddMonoidAlgebra B M) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      simp [g, RingHom.algebraMap_toAlgebra])
  let : Algebra.IsPushout A (AddMonoidAlgebra A M) B
      (AddMonoidAlgebra B M) :=
    AddMonoidAlgebra.instIsPushout'
  have hcoeff :
      (algebraMap A (AddMonoidAlgebra A M)).FaithfullyFlat := by
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  have hg' :
      (algebraMap (AddMonoidAlgebra A M)
        (AddMonoidAlgebra B M)).FormallyUnramified := by
    simpa [g, RingHom.algebraMap_toAlgebra] using hg
  have hf' :=
    RingHom.FormallyUnramified.codescendsAlong_faithfullyFlat
      (R := A) (S := B) (R' := AddMonoidAlgebra A M)
      (S' := AddMonoidAlgebra B M) hcoeff hg'
  simpa [RingHom.algebraMap_toAlgebra] using hf'

/-- Evaluation of every Laurent coordinate at one. -/
private def nestedLaurentAugmentation
    (R : Type u) [CommRing R] :
    (r : ℕ) → nestedLaurent R r →+* R
  | 0 => RingHom.id R
  | r + 1 =>
      AddMonoidAlgebra.liftNCRingHom
        (nestedLaurentAugmentation R r)
        (1 : Multiplicative ℤ →* R)
        (fun _ _ ↦ Commute.all _ _)

private theorem nestedLaurent_nontrivial
    (R : Type u) [CommRing R] [Nontrivial R] :
    ∀ r : ℕ, Nontrivial (nestedLaurent R r)
  | 0 => by
      change Nontrivial R
      infer_instance
  | r + 1 => by
      let : Nontrivial (nestedLaurent R r) :=
        nestedLaurent_nontrivial R r
      change Nontrivial (AddMonoidAlgebra (nestedLaurent R r) ℤ)
      infer_instance

/-- The canonical radical base map is faithfully flat. -/
private theorem nestedDiagonalRadicalBase_faithfullyFlat
    {R : Type u} [CommRing R] [Nontrivial R] :
    ∀ {r : ℕ} (n : Fin r → ℕ), (∀ i, 0 < n i) →
      (nestedDiagonalRadicalBase R r n).FaithfullyFlat
  | 0, _, _ => RingHom.FaithfullyFlat.of_bijective Function.bijective_id
  | r + 1, n, hn => by
      let nInit : Fin r → ℕ := Fin.init n
      let nLast : ℕ := n (Fin.last r)
      let T₀ := nestedDiagonalRadical R r nInit
      let B₀ := AddMonoidAlgebra (nestedLaurent R r) ℤ
      let A := AddMonoidAlgebra T₀ ℤ
      let uA : A := AddMonoidAlgebra.single (1 : ℤ) (1 : T₀)
      let pA : A[X] := X ^ nLast - C uA
      let f := nestedDiagonalRadicalBase R r nInit
      let g := AddMonoidAlgebra.mapRingHom ℤ f
      have hf : f.FaithfullyFlat :=
        nestedDiagonalRadicalBase_faithfullyFlat nInit
          (fun i ↦ hn i.castSucc)
      have hg : g.FaithfullyFlat :=
        mapRingHom_faithfullyFlat (M := ℤ) f hf
      let : Nontrivial (nestedLaurent R r) :=
        nestedLaurent_nontrivial R r
      let : Algebra B₀ A := g.toAlgebra
      let : Module.FaithfullyFlat B₀ A := by
        rw [← RingHom.faithfullyFlat_algebraMap_iff]
        simpa [g, RingHom.algebraMap_toAlgebra] using hg
      let : Nontrivial A := hg.injective.nontrivial
      let : Module.FaithfullyFlat A (AdjoinRoot pA) :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) uA
      have hroot : (AdjoinRoot.of pA).FaithfullyFlat := by
        rw [← AdjoinRoot.algebraMap_eq,
          RingHom.faithfullyFlat_algebraMap_iff]
        infer_instance
      have hcomp : ((AdjoinRoot.of pA).comp g).FaithfullyFlat :=
        RingHom.FaithfullyFlat.stableUnderComposition _ _ hg hroot
      change ((AdjoinRoot.of pA).comp g).FaithfullyFlat
      exact hcomp

/-- Formal unramifiedness of the dependent diagonal radical presentation
forces every positive diagonal exponent to be a unit in the coefficient ring. -/
theorem all_exponents_isUnit_of_formallyUnramified_nestedDiagonalRadical
    {R : Type u} [CommRing R] [Nontrivial R]
    {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i)
    (hFU : (nestedDiagonalRadicalBase R r n).FormallyUnramified) :
    ∀ i, IsUnit (n i : R) := by
  induction r with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ r ih =>
      let nInit : Fin r → ℕ := Fin.init n
      let nLast : ℕ := n (Fin.last r)
      let T₀ := nestedDiagonalRadical R r nInit
      let B₀ := AddMonoidAlgebra (nestedLaurent R r) ℤ
      let A := AddMonoidAlgebra T₀ ℤ
      let uA : A := AddMonoidAlgebra.single (1 : ℤ) (1 : T₀)
      let pA : A[X] := X ^ nLast - C uA
      let f := nestedDiagonalRadicalBase R r nInit
      let g := AddMonoidAlgebra.mapRingHom ℤ f
      have hfull : ((AdjoinRoot.of pA).comp g).FormallyUnramified := by
        change ((AdjoinRoot.of pA).comp g).FormallyUnramified at hFU
        exact hFU
      have hf : f.FaithfullyFlat :=
        nestedDiagonalRadicalBase_faithfullyFlat nInit
          (fun i ↦ hn i.castSucc)
      have hg : g.FaithfullyFlat :=
        mapRingHom_faithfullyFlat (M := ℤ) f hf
      let : Nontrivial (nestedLaurent R r) :=
        nestedLaurent_nontrivial R r
      let : Algebra B₀ A := g.toAlgebra
      let : Module.FaithfullyFlat B₀ A := by
        rw [← RingHom.faithfullyFlat_algebraMap_iff]
        simpa [g, RingHom.algebraMap_toAlgebra] using hg
      let : Nontrivial A := hg.injective.nontrivial
      have hFUAlg : Algebra.FormallyUnramified B₀ (AdjoinRoot pA) := by
        rw [← RingHom.formallyUnramified_algebraMap]
        simpa [g, AdjoinRoot.algebraMap_eq',
          RingHom.algebraMap_toAlgebra] using hfull
      let : Algebra.FormallyUnramified B₀ (AdjoinRoot pA) := hFUAlg
      have hnLastB₀ : IsUnit (nLast : B₀) :=
        isUnit_natCast_of_formallyUnramified_relativeRadical
          (A := B₀) (T := A) (a := uA) (n := nLast)
            (hn (Fin.last r))
      have hnLastR : IsUnit (n (Fin.last r) : R) := by
        let aug : B₀ →+* R := nestedLaurentAugmentation R (r + 1)
        have hcast : aug (nLast : B₀) = (nLast : R) :=
          map_natCast aug nLast
        simpa [nLast, aug, hcast] using hnLastB₀.map aug
      have hprefixAlg : Algebra.FormallyUnramified B₀ A :=
        formallyUnramified_prefix_of_formallyUnramified_relativeRadical
          (A := B₀) (T := A) (a := uA) (n := nLast)
            (hn (Fin.last r))
      have hgFU : g.FormallyUnramified := by
        rw [RingHom.FormallyUnramified]
        simpa [g, RingHom.algebraMap_toAlgebra] using hprefixAlg
      have hfFU : f.FormallyUnramified :=
        formallyUnramified_of_mapRingHom f hgFU
      have hInit : ∀ i : Fin r, IsUnit (n i.castSucc : R) :=
        ih nInit (fun i ↦ hn i.castSucc) hfFU
      intro i
      exact Fin.lastCases hnLastR hInit i

/-- A formally unramified finite-index lattice cover has synchronized cyclic
quotient coordinates whose orders are units in the coefficient ring.  Both
the coordinates and their unit property are produced from the lattice
inclusion and the formal-unramifiedness of its actual monoid-algebra map. -/
theorem exists_smithCyclicCoordinates_isUnit_of_formallyUnramified_latticeCover
    {R L : Type u} [CommRing R] [Nontrivial R]
    [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)]
    (hFU : (AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom).FormallyUnramified) :
    ∃ (r : ℕ) (n : Fin r → ℕ),
      (∀ i, 0 < n i) ∧
        ∃ _eQ : (L ⧸ H) ≃+ ∀ i, ZMod (n i),
          ∀ i, IsUnit (n i : R) := by
  let f := AddMonoidAlgebra.mapDomainRingHom R
    H.subtype.toAddMonoidHom
  obtain ⟨r, n, hn, eQ, eH, eL, eRad, hsquare⟩ :=
    exists_smithDiagonalRadicalPresentation (R := R) H
  have hleft : (eL.toRingHom.comp f).FormallyUnramified :=
    RingHom.FormallyUnramified.respectsIso.1 f eL hFU
  rw [hsquare] at hleft
  have hwithoutTarget :
      ((finDiagonalRadicalBase R n).comp eH.toRingHom).FormallyUnramified := by
    have h := RingHom.FormallyUnramified.respectsIso.1
      (eRad.toRingHom.comp
        ((finDiagonalRadicalBase R n).comp eH.toRingHom))
      eRad.symm hleft
    convert h using 1
    apply RingHom.ext
    intro x
    simp
  have hbase : (finDiagonalRadicalBase R n).FormallyUnramified := by
    have h := RingHom.FormallyUnramified.respectsIso.2
      ((finDiagonalRadicalBase R n).comp eH.toRingHom)
      eH.symm hwithoutTarget
    convert h using 1
    apply RingHom.ext
    intro x
    simp
  have hnUnit : ∀ i, IsUnit (n i : R) :=
    all_exponents_isUnit_of_formallyUnramified_nestedDiagonalRadical
      n hn (by
        rw [finDiagonalRadicalBase] at hbase
        exact RingHom.FormallyUnramified.of_comp hbase)
  exact ⟨r, n, hn, eQ, hnUnit⟩

end EtaleFundamentalGroups.Kummer
