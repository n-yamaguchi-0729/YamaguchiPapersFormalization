/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_RingHom_QuasiFinite_codescendsAlong_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Ring Hom Quasi Finite codescends Along faithfully Flat
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace RingHom_QuasiFinite_codescendsAlong_faithfullyFlat

universe u

open TensorProduct

namespace QFDescent

theorem of_quasiFinite_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] [Algebra.QuasiFinite T (T ⊗[R] S)] : Algebra.QuasiFinite R S := by
  refine ⟨fun P _ => ?_⟩
  obtain ⟨⟨Q, hQprime⟩, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := T)
    ⟨P, ‹_›⟩
  have hQP : Q.comap (algebraMap R T) = P := congrArg PrimeSpectrum.asIdeal hQ
  have : Q.LiesOver P := ⟨hQP.symm⟩
  let : Algebra P.ResidueField Q.ResidueField := (Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T)
    hQP.symm).toRingHom.toAlgebra
  have : IsScalarTower R P.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => ((Ideal.ResidueField.mapₐ P Q (Algebra.ofId R T)
      hQP.symm).commutes r).symm
  have hfin : Module.Finite Q.ResidueField (Q.Fiber (T ⊗[R] S)) := Algebra.QuasiFinite.finite_fiber
    Q
  let e₁ := Algebra.TensorProduct.cancelBaseChange R T Q.ResidueField Q.ResidueField S
  let e₂ := Algebra.TensorProduct.cancelBaseChange R P.ResidueField Q.ResidueField Q.ResidueField S
  have : Module.Finite Q.ResidueField (Q.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[R] S)) :=
    Module.Finite.equiv (e₁.trans e₂.symm).toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat (R := P.ResidueField) Q.ResidueField
    (M := P.ResidueField ⊗[R] S)

end QFDescent

theorem codescendsAlong_faithfullyFlat' :
    RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact QFDescent.of_quasiFinite_tensorProduct_of_faithfullyFlat S

theorem _root_.RingHom.QuasiFinite.codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.QuasiFinite R
      S _ _)
      (fun {R S : Type u} [CommRing R] [CommRing S] => @RingHom.FaithfullyFlat R S _ _) :=
  codescendsAlong_faithfullyFlat'
end AlgebraicCurves.Foundations.Algebra.Proofs.RingHom_QuasiFinite_codescendsAlong_faithfullyFlat
end ProofImplementation
