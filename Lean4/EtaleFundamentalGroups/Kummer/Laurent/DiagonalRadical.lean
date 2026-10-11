/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Basic
import EtaleFundamentalGroups.Kummer.Laurent.CyclicCover
import EtaleFundamentalGroups.Kummer.Lattices.Smith.SignNormalization

/-!
# Finite diagonal Laurent covers as iterated radicals

This file builds a finite diagonal Laurent cover one coordinate at a time.
At each successor step, the preceding radical is extended by one Laurent
coordinate and the one-variable cyclic Laurent equivalence removes the new
diagonal exponent.  All maps are explicit ring homomorphisms; no noncanonical
algebra structures or scalar towers are installed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The Laurent algebra obtained by adjoining `r` independent Laurent coordinates. -/
def nestedLaurent (R : Type u) [CommRing R] : ℕ → CommRingCat.{u}
  | 0 => CommRingCat.of R
  | r + 1 => CommRingCat.of (AddMonoidAlgebra (nestedLaurent R r) ℤ)

/--
The radical presentation built in parallel with `nestedLaurent`.  At each
successor step a root of the new degree-one Laurent monomial is adjoined.
-/
def nestedDiagonalRadical (R : Type u) [CommRing R] :
    (r : ℕ) → (Fin r → ℕ) → CommRingCat.{u}
  | 0, _ => CommRingCat.of R
  | r + 1, n =>
      CommRingCat.of (AdjoinRoot
        (X ^ n (Fin.last r) -
          C (AddMonoidAlgebra.single (1 : ℤ) (1 :
            nestedDiagonalRadical R r (Fin.init n)))))

/-- The canonical base map from the nested Laurent algebra into its radical presentation. -/
def nestedDiagonalRadicalBase (R : Type u) [CommRing R] :
    (r : ℕ) → (n : Fin r → ℕ) →
      nestedLaurent R r →+* nestedDiagonalRadical R r n
  | 0, _ => RingHom.id R
  | r + 1, n =>
      let p := X ^ n (Fin.last r) -
        C (AddMonoidAlgebra.single (1 : ℤ) (1 :
          nestedDiagonalRadical R r (Fin.init n)))
      (AdjoinRoot.of p).comp
        (AddMonoidAlgebra.mapRingHom ℤ
          (nestedDiagonalRadicalBase R r (Fin.init n)))

/-- The coordinatewise diagonal endomorphism of the nested Laurent algebra. -/
def nestedLaurentDiagonalMap (R : Type u) [CommRing R] :
    (r : ℕ) → (n : Fin r → ℕ) → nestedLaurent R r →+* nestedLaurent R r
  | 0, _ => RingHom.id R
  | r + 1, n =>
      (AddMonoidAlgebra.mapDomainRingHom (nestedLaurent R r)
        (nsmulAddMonoidHom (n (Fin.last r)))).comp
        (AddMonoidAlgebra.mapRingHom ℤ
          (nestedLaurentDiagonalMap R r (Fin.init n)))

/-- Split a tuple into its last coordinate and its initial tuple. -/
private def finLastInitAddEquiv (r : ℕ) :
    (Fin (r + 1) → ℤ) ≃+ (ℤ × (Fin r → ℤ)) :=
  { (Fin.snocEquiv (fun _ : Fin (r + 1) ↦ ℤ)).symm with
    map_add' := by
      intro x y
      ext <;> rfl }

/-- A monomial in the nested Laurent presentation. -/
private def nestedLaurentMonomial (R : Type u) [CommRing R] :
    (r : ℕ) → (Fin r → ℤ) → R → nestedLaurent R r
  | 0, _, a => a
  | r + 1, x, a =>
      AddMonoidAlgebra.single (x (Fin.last r))
        (nestedLaurentMonomial R r (Fin.init x) a)

/-- The ordinary `Fin r` Laurent algebra as the nested Laurent presentation. -/
private def finLaurentRingEquiv (R : Type u) [CommRing R] :
    (r : ℕ) → AddMonoidAlgebra R (Fin r → ℤ) ≃+* nestedLaurent R r
  | 0 => (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).toRingEquiv
  | r + 1 =>
      (((AddMonoidAlgebra.domCongr R R (finLastInitAddEquiv r)).trans
        (AddMonoidAlgebra.curryAlgEquiv R)).toRingEquiv).trans
          (AddMonoidAlgebra.mapRingEquiv ℤ (finLaurentRingEquiv R r))

private theorem finLaurentRingEquiv_single
    {R : Type u} [CommRing R] :
    ∀ {r : ℕ} (x : Fin r → ℤ) (a : R),
      finLaurentRingEquiv R r (AddMonoidAlgebra.single x a) =
        nestedLaurentMonomial R r x a
  | 0, x, a => by
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      change
        (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).toRingEquiv
            (AddMonoidAlgebra.single 0 a) = a
      apply (AddMonoidAlgebra.uniqueAlgEquiv R (Fin 0 → ℤ)).symm.injective
      simp
  | r + 1, x, a => by
      change
        AddMonoidAlgebra.mapRingEquiv ℤ (finLaurentRingEquiv R r)
          (AddMonoidAlgebra.curryAlgEquiv R
            (AddMonoidAlgebra.domCongr R R (finLastInitAddEquiv r)
              (AddMonoidAlgebra.single x a))) =
          AddMonoidAlgebra.single (x (Fin.last r))
            (nestedLaurentMonomial R r (Fin.init x) a)
      rw [AddMonoidAlgebra.domCongr_single]
      change
        AddMonoidAlgebra.mapRingEquiv ℤ (finLaurentRingEquiv R r)
          (AddMonoidAlgebra.curryAlgEquiv R
            (AddMonoidAlgebra.single
              (x (Fin.last r), Fin.init x) a)) = _
      rw [AddMonoidAlgebra.curryAlgEquiv_single,
        AddMonoidAlgebra.mapRingEquiv_single,
        finLaurentRingEquiv_single]

/-- Coordinatewise multiplication by the positive diagonal entries. -/
private def finDiagonalAddMonoidHom {r : ℕ} (n : Fin r → ℕ) :
    (Fin r → ℤ) →+ (Fin r → ℤ) where
  toFun x i := (n i : ℤ) * x i
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]

private theorem nestedLaurentDiagonalMap_monomial
    {R : Type u} [CommRing R] :
    ∀ {r : ℕ} (n : Fin r → ℕ) (x : Fin r → ℤ) (a : R),
      nestedLaurentDiagonalMap R r n (nestedLaurentMonomial R r x a) =
        nestedLaurentMonomial R r (finDiagonalAddMonoidHom n x) a
  | 0, _, _, _ => rfl
  | r + 1, n, x, a => by
      change
        AddMonoidAlgebra.mapDomainRingHom (nestedLaurent R r)
            (nsmulAddMonoidHom (n (Fin.last r)))
            (AddMonoidAlgebra.mapRingHom ℤ
              (nestedLaurentDiagonalMap R r (Fin.init n))
              (AddMonoidAlgebra.single (x (Fin.last r))
                (nestedLaurentMonomial R r (Fin.init x) a))) =
          AddMonoidAlgebra.single
            ((n (Fin.last r) : ℤ) * x (Fin.last r))
            (nestedLaurentMonomial R r
              (finDiagonalAddMonoidHom (Fin.init n) (Fin.init x)) a)
      rw [AddMonoidAlgebra.mapRingHom_single,
        nestedLaurentDiagonalMap_monomial]
      change
        AddMonoidAlgebra.mapDomain (nsmulAddMonoidHom (n (Fin.last r)))
            (AddMonoidAlgebra.single (x (Fin.last r))
              (nestedLaurentMonomial R r
                (finDiagonalAddMonoidHom (Fin.init n) (Fin.init x)) a)) = _
      rw [AddMonoidAlgebra.mapDomain_single]
      rfl

/-- The finite-coordinate Laurent equivalence conjugates the two diagonal maps. -/
private theorem finLaurentRingEquiv_comp_diagonal
    {R : Type u} [CommRing R] {r : ℕ} (n : Fin r → ℕ) :
    (finLaurentRingEquiv R r).toRingHom.comp
        (AddMonoidAlgebra.mapDomainRingHom R (finDiagonalAddMonoidHom n)) =
      (nestedLaurentDiagonalMap R r n).comp
        (finLaurentRingEquiv R r).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    simp [AddMonoidAlgebra.mapDomain_single,
      finLaurentRingEquiv_single,
      nestedLaurentDiagonalMap_monomial, finDiagonalAddMonoidHom]
  · intro x
    simp [AddMonoidAlgebra.mapDomain_single,
      finLaurentRingEquiv_single,
      nestedLaurentDiagonalMap_monomial, finDiagonalAddMonoidHom]

/--
Positive diagonal exponents give an iterated radical ring equivalent to the
nested Laurent algebra, with the equivalence restricting to the full diagonal
endomorphism on the original base.
-/
theorem exists_nestedDiagonalRadicalRingEquiv
    {R : Type u} [CommRing R] :
    ∀ {r : ℕ} (n : Fin r → ℕ), (∀ i, 0 < n i) →
      ∃ e : nestedDiagonalRadical R r n ≃+* nestedLaurent R r,
        e.toRingHom.comp (nestedDiagonalRadicalBase R r n) =
          nestedLaurentDiagonalMap R r n
  | 0, _, _ => ⟨RingEquiv.refl R, rfl⟩
  | r + 1, n, hn => by
      let nInit : Fin r → ℕ := Fin.init n
      let nLast : ℕ := n (Fin.last r)
      let L₀ := nestedLaurent R r
      let T₀ := nestedDiagonalRadical R r nInit
      let A := AddMonoidAlgebra T₀ ℤ
      let B := AddMonoidAlgebra L₀ ℤ
      let uA : A := AddMonoidAlgebra.single (1 : ℤ) (1 : T₀)
      let uB : B := AddMonoidAlgebra.single (1 : ℤ) (1 : L₀)
      let pA : A[X] := X ^ nLast - C uA
      let pB : B[X] := X ^ nLast - C uB
      obtain ⟨e₀, he₀⟩ :=
        exists_nestedDiagonalRadicalRingEquiv (R := R) (r := r)
          nInit (fun i ↦ hn i.castSucc)
      let c : A ≃+* B := AddMonoidAlgebra.mapRingEquiv ℤ e₀
      have hc :
          (AddMonoidAlgebra.mapRingHom ℤ e₀.toRingHom).comp
              (AddMonoidAlgebra.mapRingHom ℤ
                (nestedDiagonalRadicalBase R r nInit)) =
            AddMonoidAlgebra.mapRingHom ℤ
              (nestedLaurentDiagonalMap R r nInit) := by
        rw [← AddMonoidAlgebra.mapRingHom_comp, he₀]
      have hcu : c uA = uB := by
        simpa [c, uA, uB] using
          (AddMonoidAlgebra.mapRingEquiv_single (M := ℤ)
            e₀ (1 : T₀) (1 : ℤ))
      have hp : Associated (pA.map c) pB := by
        have h : pA.map c = pB := by
          simp [pA, pB, hcu]
        rw [h]
      let transport : AdjoinRoot pA ≃+* AdjoinRoot pB :=
        AdjoinRoot.mapRingEquiv c pA pB hp
      obtain ⟨eLast, _, heLast⟩ :=
        exists_cyclicLaurentRingEquiv (R := L₀) nLast (hn (Fin.last r))
      let e : AdjoinRoot pA ≃+* B := transport.trans eLast
      refine ⟨e, ?_⟩
      apply RingHom.ext
      intro x
      change eLast (transport
        (AdjoinRoot.of pA
          (AddMonoidAlgebra.mapRingHom ℤ
            (nestedDiagonalRadicalBase R r nInit) x))) = _
      rw [show transport (AdjoinRoot.of pA
          (AddMonoidAlgebra.mapRingHom ℤ
            (nestedDiagonalRadicalBase R r nInit) x)) =
          AdjoinRoot.of pB
            (c (AddMonoidAlgebra.mapRingHom ℤ
              (nestedDiagonalRadicalBase R r nInit) x)) by
        simp [transport]]
      rw [show eLast (AdjoinRoot.of pB
          (c (AddMonoidAlgebra.mapRingHom ℤ
            (nestedDiagonalRadicalBase R r nInit) x))) =
          AddMonoidAlgebra.mapDomainRingHom L₀
            (nsmulAddMonoidHom nLast)
            (c (AddMonoidAlgebra.mapRingHom ℤ
              (nestedDiagonalRadicalBase R r nInit) x)) by
        exact RingHom.congr_fun heLast _]
      change
        AddMonoidAlgebra.mapDomainRingHom L₀
            (nsmulAddMonoidHom nLast)
            (AddMonoidAlgebra.mapRingHom ℤ e₀
              (AddMonoidAlgebra.mapRingHom ℤ
                (nestedDiagonalRadicalBase R r nInit) x)) =
          AddMonoidAlgebra.mapDomainRingHom L₀
            (nsmulAddMonoidHom nLast)
            (AddMonoidAlgebra.mapRingHom ℤ
              (nestedLaurentDiagonalMap R r nInit) x)
      congr 1
      exact RingHom.congr_fun hc x

/-- The base map from the ordinary finite-coordinate Laurent algebra to the
corresponding nested radical presentation. -/
def finDiagonalRadicalBase
    (R : Type u) [CommRing R] {r : ℕ} (n : Fin r → ℕ) :
    AddMonoidAlgebra R (Fin r → ℤ) →+* nestedDiagonalRadical R r n :=
  (nestedDiagonalRadicalBase R r n).comp
    (finLaurentRingEquiv R r).toRingHom

/-- The diagonal endomorphism on the ordinary finite-coordinate Laurent algebra. -/
def finLaurentDiagonalMap
    (R : Type u) [CommRing R] {r : ℕ} (n : Fin r → ℕ) :
    AddMonoidAlgebra R (Fin r → ℤ) →+* AddMonoidAlgebra R (Fin r → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom R (finDiagonalAddMonoidHom n)

/--
The nested radical presentation is a finite-coordinate Laurent algebra, and
its base map is exactly the coordinatewise positive diagonal map.
-/
theorem exists_finDiagonalRadicalRingEquiv
    {R : Type u} [CommRing R] {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) :
    ∃ e : nestedDiagonalRadical R r n ≃+*
        AddMonoidAlgebra R (Fin r → ℤ),
      e.toRingHom.comp (finDiagonalRadicalBase R n) =
        finLaurentDiagonalMap R n := by
  obtain ⟨eNested, heNested⟩ :=
    exists_nestedDiagonalRadicalRingEquiv (R := R) n hn
  let eFin := finLaurentRingEquiv R r
  let e : nestedDiagonalRadical R r n ≃+*
      AddMonoidAlgebra R (Fin r → ℤ) := eNested.trans eFin.symm
  refine ⟨e, ?_⟩
  apply RingHom.ext
  intro x
  have hNested := RingHom.congr_fun heNested (eFin x)
  have hDiagonal :=
    RingHom.congr_fun (finLaurentRingEquiv_comp_diagonal (R := R) n) x
  change eNested (nestedDiagonalRadicalBase R r n (eFin x)) =
    nestedLaurentDiagonalMap R r n (eFin x) at hNested
  change eFin (AddMonoidAlgebra.mapDomainRingHom R
      (finDiagonalAddMonoidHom n) x) =
    nestedLaurentDiagonalMap R r n (eFin x) at hDiagonal
  change eFin.symm (eNested
      (nestedDiagonalRadicalBase R r n (eFin x))) =
    AddMonoidAlgebra.mapDomainRingHom R (finDiagonalAddMonoidHom n) x
  rw [hNested, ← hDiagonal, eFin.symm_apply_apply]

/-- Reindex a finite family by its canonical equivalence with `Fin`. -/
private def fintypeReindexAddEquiv (ι : Type u) [Fintype ι] :
    (ι → ℤ) ≃+ (Fin (Fintype.card ι) → ℤ) where
  toFun x j := x ((Fintype.equivFin ι).symm j)
  invFun y i := y (Fintype.equivFin ι i)
  left_inv x := by
    ext i
    simp
  right_inv y := by
    ext j
    simp
  map_add' x y := by
    ext j
    rfl

/-- Reindex the cyclic Smith quotient coordinates by `Fintype.equivFin`. -/
private def fintypeReindexZModAddEquiv (ι : Type u) [Fintype ι]
    (n : ι → ℕ) :
    (∀ i, ZMod (n i)) ≃+
      (∀ j : Fin (Fintype.card ι),
        ZMod (n ((Fintype.equivFin ι).symm j))) :=
  (LinearEquiv.piCongrLeft' ℤ (fun i ↦ ZMod (n i))
    (Fintype.equivFin ι)).toAddEquiv

/--
A finite-index free integer sublattice gives an explicit finite iterated
radical presentation of its monoid-algebra map.  The positive diagonal entries,
the quotient coordinates, the monoid-algebra coordinate changes, and the
commutative square are all produced from the same Smith choice for the lattice
inclusion.
-/
theorem exists_smithDiagonalRadicalPresentation
    {R L : Type u} [CommRing R] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    ∃ (r : ℕ) (n : Fin r → ℕ),
      (∀ i, 0 < n i) ∧
        ∃ (_eQ : (L ⧸ H) ≃+ ∀ i, ZMod (n i))
          (eH : AddMonoidAlgebra R H ≃+*
              AddMonoidAlgebra R (Fin r → ℤ))
          (eL : AddMonoidAlgebra R L ≃+*
              AddMonoidAlgebra R (Fin r → ℤ))
          (eRad : nestedDiagonalRadical R r n ≃+*
              AddMonoidAlgebra R (Fin r → ℤ)),
          eL.toRingHom.comp
              (AddMonoidAlgebra.mapDomainRingHom R
                H.subtype.toAddMonoidHom) =
            eRad.toRingHom.comp
              ((finDiagonalRadicalBase R n).comp eH.toRingHom) := by
  obtain ⟨ι, instι, n, hn, eH, eL, d, eQ, hd, hsquare⟩ :=
    exists_smithNatDiagonal_monoidAlgebra (R := R) H
  let : Fintype ι := instι
  let r := Fintype.card ι
  let idx := Fintype.equivFin ι
  let q : (ι → ℤ) ≃+ (Fin r → ℤ) := fintypeReindexAddEquiv ι
  let nFin : Fin r → ℕ := fun j ↦ n (idx.symm j)
  let eQFin : (L ⧸ H) ≃+ ∀ j, ZMod (nFin j) :=
    eQ.trans (fintypeReindexZModAddEquiv ι n)
  let diagonalFin : (Fin r → ℤ) →+ (Fin r → ℤ) :=
    finDiagonalAddMonoidHom nFin
  have hnFin : ∀ j, 0 < nFin j := fun j ↦ hn (idx.symm j)
  have hdFin : q.toAddMonoidHom.comp d =
      diagonalFin.comp q.toAddMonoidHom := by
    ext x j
    change d x (idx.symm j) =
      (n (idx.symm j) : ℤ) * x (idx.symm j)
    exact hd x (idx.symm j)
  let eHFin : AddMonoidAlgebra R H ≃+*
      AddMonoidAlgebra R (Fin r → ℤ) :=
    (AddMonoidAlgebra.domCongr R R (eH.trans q)).toRingEquiv
  let eLFin : AddMonoidAlgebra R L ≃+*
      AddMonoidAlgebra R (Fin r → ℤ) :=
    (AddMonoidAlgebra.domCongr R R (eL.trans q)).toRingEquiv
  have hqmap :
      (AddMonoidAlgebra.mapDomainAlgHom R R q.toAddMonoidHom).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R d) =
        (AddMonoidAlgebra.mapDomainAlgHom R R diagonalFin).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R q.toAddMonoidHom) := by
    rw [← AddMonoidAlgebra.mapDomainAlgHom_comp,
      ← AddMonoidAlgebra.mapDomainAlgHom_comp, hdFin]
  have hsquareMap := hsquare
  rw [AddMonoidAlgebra.domCongr_toAlgHom,
    AddMonoidAlgebra.domCongr_toAlgHom] at hsquareMap
  change
    (AddMonoidAlgebra.mapDomainAlgHom R R eL.toAddMonoidHom).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R
          H.subtype.toAddMonoidHom) =
      (AddMonoidAlgebra.mapDomainAlgHom R R d).comp
        (AddMonoidAlgebra.mapDomainAlgHom R R eH.toAddMonoidHom)
    at hsquareMap
  have hsquareFinAlg :
      (AddMonoidAlgebra.domCongr R R (eL.trans q)).toAlgHom.comp
          (AddMonoidAlgebra.mapDomainAlgHom R R
            H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R diagonalFin).comp
          (AddMonoidAlgebra.domCongr R R (eH.trans q)).toAlgHom := by
    rw [AddMonoidAlgebra.domCongr_toAlgHom,
      AddMonoidAlgebra.domCongr_toAlgHom]
    change
      (AddMonoidAlgebra.mapDomainAlgHom R R
          (q.toAddMonoidHom.comp eL.toAddMonoidHom)).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R
            H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainAlgHom R R diagonalFin).comp
          (AddMonoidAlgebra.mapDomainAlgHom R R
            (q.toAddMonoidHom.comp eH.toAddMonoidHom))
    rw [AddMonoidAlgebra.mapDomainAlgHom_comp,
      AddMonoidAlgebra.mapDomainAlgHom_comp]
    rw [AlgHom.comp_assoc, hsquareMap, ← AlgHom.comp_assoc,
      hqmap, AlgHom.comp_assoc]
  have hsquareFin :
      eLFin.toRingHom.comp
          (AddMonoidAlgebra.mapDomainRingHom R
            H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainRingHom R diagonalFin).comp
          eHFin.toRingHom := by
    exact congrArg AlgHom.toRingHom hsquareFinAlg
  obtain ⟨eRad, heRad⟩ :=
    exists_finDiagonalRadicalRingEquiv (R := R) nFin hnFin
  refine ⟨r, nFin, hnFin, eQFin, eHFin, eLFin, eRad, ?_⟩
  calc
    eLFin.toRingHom.comp
          (AddMonoidAlgebra.mapDomainRingHom R
            H.subtype.toAddMonoidHom) =
        (AddMonoidAlgebra.mapDomainRingHom R diagonalFin).comp
          eHFin.toRingHom := hsquareFin
    _ = (finLaurentDiagonalMap R nFin).comp eHFin.toRingHom := by
      rfl
    _ = (eRad.toRingHom.comp (finDiagonalRadicalBase R nFin)).comp
          eHFin.toRingHom := by rw [heRad]
    _ = eRad.toRingHom.comp
          ((finDiagonalRadicalBase R nFin).comp eHFin.toRingHom) := by
      rw [RingHom.comp_assoc]

end EtaleFundamentalGroups.Kummer
