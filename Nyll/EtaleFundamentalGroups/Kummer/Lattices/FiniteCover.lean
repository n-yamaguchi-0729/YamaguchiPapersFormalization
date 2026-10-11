/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Nyll.EtaleFundamentalGroups.Kummer.Laurent.DiagonalRadical

/-!
# Finiteness of finite-index lattice covers

The Smith presentation of a finite-index lattice inclusion is an iterated
monic radical extension.  This file uses that presentation to prove that the
induced monoid-algebra map is finite.  Coefficient extension for monoid
algebras is handled by its canonical pushout square, so no persistent custom
algebra or scalar-tower instances are introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- Extending coefficients in an additive monoid algebra preserves finiteness
of a ring homomorphism. -/
private theorem mapRingHom_isFinite
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommMonoid M]
    (f : A →+* B) (hf : f.Finite) :
    (AddMonoidAlgebra.mapRingHom M f).Finite := by
  let g := AddMonoidAlgebra.mapRingHom M f
  let : Algebra A B := f.toAlgebra
  let : Algebra (AddMonoidAlgebra A M) (AddMonoidAlgebra B M) :=
    g.toAlgebra
  let : Module.Finite A B := hf
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
  let : Module.Finite (AddMonoidAlgebra A M)
      (TensorProduct A (AddMonoidAlgebra A M) B) :=
    Module.Finite.base_change A (AddMonoidAlgebra A M) B
  exact Module.Finite.equiv
    (Algebra.IsPushout.equiv A (AddMonoidAlgebra A M) B
      (AddMonoidAlgebra B M)).toLinearEquiv

/-- The canonical map into the recursively constructed radical algebra is
finite because every successor polynomial is monic. -/
private theorem nestedDiagonalRadicalBase_isFinite
    {R : Type u} [CommRing R] :
    ∀ {r : ℕ} (n : Fin r → ℕ), (∀ i, 0 < n i) →
      (nestedDiagonalRadicalBase R r n).Finite
  | 0, _, _ => RingHom.Finite.id R
  | r + 1, n, hn => by
      let nInit : Fin r → ℕ := Fin.init n
      let nLast : ℕ := n (Fin.last r)
      let T₀ := nestedDiagonalRadical R r nInit
      let A := AddMonoidAlgebra T₀ ℤ
      let uA : A := AddMonoidAlgebra.single (1 : ℤ) (1 : T₀)
      let pA : A[X] := X ^ nLast - C uA
      have hInit :
          (nestedDiagonalRadicalBase R r nInit).Finite :=
        nestedDiagonalRadicalBase_isFinite nInit
          (fun i => hn i.castSucc)
      have hMap :
          (AddMonoidAlgebra.mapRingHom ℤ
            (nestedDiagonalRadicalBase R r nInit)).Finite :=
        mapRingHom_isFinite _ hInit
      have hpA : pA.Monic :=
        Polynomial.monic_X_pow_sub_C uA (hn (Fin.last r)).ne'
      let : Module.Finite A (AdjoinRoot pA) := hpA.finite_adjoinRoot
      have hRoot : (AdjoinRoot.of pA).Finite :=
        RingHom.finite_algebraMap.mpr inferInstance
      exact RingHom.Finite.comp hRoot hMap

/-- The finite-coordinate radical base map is finite. -/
private theorem finDiagonalRadicalBase_isFinite
    {R : Type u} [CommRing R] {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) :
    (finDiagonalRadicalBase R n).Finite := by
  rw [finDiagonalRadicalBase]
  exact RingHom.Finite.comp
    (nestedDiagonalRadicalBase_isFinite n hn)
    (RingEquiv.finite _)

/--
The monoid-algebra map of a finite-index inclusion of finite free integer
lattices is finite.  Positivity and the diagonal radical presentation are
generated from the inclusion itself; no normalization comparison is assumed.
-/
theorem latticeMonoidAlgebraMap_isFinite
    {R L : Type u} [CommRing R] [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L]
    (H : Submodule ℤ L) [Finite (L ⧸ H)] :
    (AddMonoidAlgebra.mapDomainRingHom R
      H.subtype.toAddMonoidHom).Finite := by
  obtain ⟨r, n, hn, _eQ, eH, eL, eRad, hsquare⟩ :=
    exists_smithDiagonalRadicalPresentation (R := R) H
  have hbase : (finDiagonalRadicalBase R n).Finite :=
    finDiagonalRadicalBase_isFinite n hn
  have hright :
      (eRad.toRingHom.comp
        ((finDiagonalRadicalBase R n).comp eH.toRingHom)).Finite :=
    RingHom.Finite.comp eRad.finite
      (RingHom.Finite.comp hbase eH.finite)
  have hleft :
      (eL.toRingHom.comp
        (AddMonoidAlgebra.mapDomainRingHom R
          H.subtype.toAddMonoidHom)).Finite := by
    rw [hsquare]
    exact hright
  have hrecover :
      (eL.symm.toRingHom.comp
        (eL.toRingHom.comp
          (AddMonoidAlgebra.mapDomainRingHom R
            H.subtype.toAddMonoidHom))).Finite :=
    RingHom.Finite.comp eL.symm.finite hleft
  simpa [← RingHom.comp_assoc] using hrecover

end EtaleFundamentalGroups.Kummer
