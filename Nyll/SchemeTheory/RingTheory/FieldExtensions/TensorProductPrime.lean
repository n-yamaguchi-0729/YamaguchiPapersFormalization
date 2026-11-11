/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Compatible prime ideals lift to a tensor product

Two prime ideals of algebras over the same ring lift simultaneously to the
tensor product when their contractions agree. The point is constructed in
the scheme fiber product after lifting the rings to a common universe.
The actual tensor-product equivalence then transports the point back,
with both original projections verified.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace PrimeSpectrum

universe u v w

private theorem exists_tensorProduct_of_comap_eq_sameUniverse
    (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C]
    (p : PrimeSpectrum B) (q : PrimeSpectrum C)
    (h : comap (algebraMap R B) p = comap (algebraMap R C) q) :
    ∃ r : PrimeSpectrum (B ⊗[R] C),
      comap (algebraMap B (B ⊗[R] C)) r = p ∧
        comap (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom r = q := by
  let f : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let g : Spec (.of C) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R C))
  obtain ⟨z, hzB, hzC⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) p q h
  refine ⟨(pullbackSpecIso R B C).hom z, ?_, ?_⟩
  · exact (congrArg (fun k : pullback f g ⟶ Spec (.of B) ↦ k z)
      (pullbackSpecIso_hom_fst' R B C)).trans hzB
  · exact (congrArg (fun k : pullback f g ⟶ Spec (.of C) ↦ k z)
      (pullbackSpecIso_hom_snd R B C)).trans hzC

attribute [local instance] ULift.algebra' in
/-- Compatible prime ideals of algebras in independent universes lift to a prime of
their tensor product, with both contractions prescribed. No dominance or flatness
assumption is required. -/
theorem exists_tensorProduct_of_comap_eq
    (R : Type u) (B : Type v) (C : Type w)
    [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (p : PrimeSpectrum B) (q : PrimeSpectrum C)
    (h : comap (algebraMap R B) p = comap (algebraMap R C) q) :
    ∃ r : PrimeSpectrum (B ⊗[R] C),
      comap (algebraMap B (B ⊗[R] C)) r = p ∧
        comap (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom r = q := by
  let R' := ULift.{max u v w} R
  let B' := ULift.{max u v w} B
  let C' := ULift.{max u v w} C
  let p' : PrimeSpectrum B' := comap ULift.ringEquiv.toRingHom p
  let q' : PrimeSpectrum C' := comap ULift.ringEquiv.toRingHom q
  have h' : comap (algebraMap R' B') p' = comap (algebraMap R' C') q' := by
    change comap (ULift.ringEquiv : R' ≃+* R).toRingHom
        (comap (algebraMap R B) p) =
      comap (ULift.ringEquiv : R' ≃+* R).toRingHom
        (comap (algebraMap R C) q)
    exact congrArg (comap (ULift.ringEquiv : R' ≃+* R).toRingHom) h
  obtain ⟨r, hrB, hrC⟩ :=
    exists_tensorProduct_of_comap_eq_sameUniverse R' B' C' p' q' h'
  let e : ULift.{max u v w} (B ⊗[R] C) ≃ₐ[R] B' ⊗[R'] C' :=
    Algebra.TensorProduct.uliftEquiv R R B C
  let j : B ⊗[R] C →+* B' ⊗[R'] C' :=
    e.toRingHom.comp ULift.ringEquiv.symm.toRingHom
  have hjB : j.comp (algebraMap B (B ⊗[R] C)) =
      (algebraMap B' (B' ⊗[R'] C')).comp
        (ULift.ringEquiv : B' ≃+* B).symm.toRingHom := by
    ext b
    change e ⟨b ⊗ₜ[R] (1 : C)⟩ = (⟨b⟩ : B') ⊗ₜ[R'] (⟨1⟩ : C')
    rfl
  have hjC : j.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := B)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := R') (A := B')).toRingHom.comp
        (ULift.ringEquiv : C' ≃+* C).symm.toRingHom := by
    ext c
    change e ⟨(1 : B) ⊗ₜ[R] c⟩ = (⟨1⟩ : B') ⊗ₜ[R'] (⟨c⟩ : C')
    rfl
  refine ⟨comap j r, ?_, ?_⟩
  · rw [← comap_comp_apply, hjB]
    exact congrArg (comap (ULift.ringEquiv : B' ≃+* B).symm.toRingHom) hrB
  · rw [← comap_comp_apply, hjC]
    exact congrArg (comap (ULift.ringEquiv : C' ≃+* C).symm.toRingHom) hrC

end PrimeSpectrum
