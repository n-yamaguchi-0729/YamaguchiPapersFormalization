/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RingHom.Integral
import Nyll.EtaleFundamentalGroups.Kummer.Laurent.DiagonalRadical

/-!
# Integrality of finite-index lattice covers

The Smith presentation of a finite-index lattice inclusion is an iterated
monic radical extension.  This file uses that presentation to prove that the
original monoid-algebra map is integral.  It is the first ring-theoretic input
needed to compare the explicit cover with an actual normalization.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- Extending coefficients in an additive monoid algebra preserves
integrality of a ring homomorphism. -/
private theorem mapRingHom_isIntegral
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommMonoid M]
    (f : A →+* B) (hf : f.IsIntegral) :
    (AddMonoidAlgebra.mapRingHom M f).IsIntegral := by
  let g := AddMonoidAlgebra.mapRingHom M f
  intro x
  induction x using AddMonoidAlgebra.induction_on with
  | of m =>
      change g.IsIntegralElem (AddMonoidAlgebra.single m 1)
      simpa [g] using
        (g.isIntegralElem_map
          (x := AddMonoidAlgebra.single m (1 : A)))
  | add x y hx hy =>
      exact hx.add g hy
  | smul b x hx =>
      have hcomp :
          (AddMonoidAlgebra.singleZeroRingHom (R := B) (M := M)).comp f =
            g.comp (AddMonoidAlgebra.singleZeroRingHom (R := A) (M := M)) := by
        ext a
        simp [g]
      have hbComp :
          (g.comp (AddMonoidAlgebra.singleZeroRingHom
            (R := A) (M := M))).IsIntegralElem
            (AddMonoidAlgebra.single 0 b) := by
        rw [← hcomp]
        exact (hf b).map
          (AddMonoidAlgebra.singleZeroRingHom (R := B) (M := M))
      have hb : g.IsIntegralElem (AddMonoidAlgebra.single 0 b) :=
        RingHom.isIntegralElem.of_comp
          (AddMonoidAlgebra.singleZeroRingHom (R := A) (M := M)) g hbComp
      simpa [Algebra.smul_def] using hb.mul g hx

/-- The canonical map into the recursively constructed radical algebra is
integral because every successor polynomial is monic. -/
private theorem nestedDiagonalRadicalBase_isIntegral
    {R : Type u} [CommRing R] :
    ∀ {r : ℕ} (n : Fin r → ℕ), (∀ i, 0 < n i) →
      (nestedDiagonalRadicalBase R r n).IsIntegral
  | 0, _, _ => fun x ↦ (RingHom.id R).isIntegralElem_map
  | r + 1, n, hn => by
      let nInit : Fin r → ℕ := Fin.init n
      let nLast : ℕ := n (Fin.last r)
      let T₀ := nestedDiagonalRadical R r nInit
      let A := AddMonoidAlgebra T₀ ℤ
      let uA : A := AddMonoidAlgebra.single (1 : ℤ) (1 : T₀)
      let pA : A[X] := X ^ nLast - C uA
      have hInit :
          (nestedDiagonalRadicalBase R r nInit).IsIntegral :=
        nestedDiagonalRadicalBase_isIntegral nInit
          (fun i ↦ hn i.castSucc)
      have hMap :
          (AddMonoidAlgebra.mapRingHom ℤ
            (nestedDiagonalRadicalBase R r nInit)).IsIntegral :=
        mapRingHom_isIntegral _ hInit
      have hpA : pA.Monic :=
        Polynomial.monic_X_pow_sub_C uA (hn (Fin.last r)).ne'
      let : Module.Finite A (AdjoinRoot pA) := hpA.finite_adjoinRoot
      have hRoot : (AdjoinRoot.of pA).IsIntegral :=
        (RingHom.finite_algebraMap.mpr inferInstance).to_isIntegral
      exact hMap.trans _ _ hRoot

/-- The finite-coordinate radical base map is integral. -/
private theorem finDiagonalRadicalBase_isIntegral
    {R : Type u} [CommRing R] {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) :
    (finDiagonalRadicalBase R n).IsIntegral := by
  rw [finDiagonalRadicalBase]
  exact (RingEquiv.finite _).to_isIntegral |>.trans _ _
    (nestedDiagonalRadicalBase_isIntegral n hn)

/--
The monoid-algebra map of a finite-index inclusion of finite free integer
lattices is integral.  Positivity and the diagonal radical presentation are
generated from the inclusion itself; no normalization comparison is assumed.
-/
theorem latticeMonoidAlgebraMap_isIntegral
    {R L : Type u} [CommRing R] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    (AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom).IsIntegral := by
  obtain ⟨r, n, hn, _eQ, eH, eL, eRad, hsquare⟩ :=
    exists_smithDiagonalRadicalPresentation (R := R) H
  have heH : eH.toRingHom.IsIntegral := eH.finite.to_isIntegral
  have hbase : (finDiagonalRadicalBase R n).IsIntegral :=
    finDiagonalRadicalBase_isIntegral n hn
  have heRad : eRad.toRingHom.IsIntegral := eRad.finite.to_isIntegral
  have hright :
      (eRad.toRingHom.comp
        ((finDiagonalRadicalBase R n).comp eH.toRingHom)).IsIntegral :=
    (heH.trans _ _ hbase).trans _ _ heRad
  have hleft :
      (eL.toRingHom.comp
        (AddMonoidAlgebra.mapDomainRingHom R
          H.subtype.toAddMonoidHom)).IsIntegral := by
    rw [hsquare]
    exact hright
  exact RingHom.IsIntegral.tower_bot _ eL.toRingHom eL.injective hleft

end EtaleFundamentalGroups.Kummer
