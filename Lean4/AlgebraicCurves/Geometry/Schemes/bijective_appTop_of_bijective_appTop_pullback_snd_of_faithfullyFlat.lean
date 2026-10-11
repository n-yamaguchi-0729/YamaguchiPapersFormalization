/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat

/-!
# bijective app Top of bijective app Top pullback snd of faithfully Flat
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem _root_.AlgebraicGeometry.bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
    {k : Type u} [CommRing k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type u) [CommRing A] [Algebra k A] [Module.FaithfullyFlat k A]
    (hA : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom) :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom := by
  have : Module.Flat k A := inferInstance
  let alg : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    fX.appTop).hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap k Γ(X, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    fX.appTop :=
    CommRingCat.ofHom_hom _
  have h := AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat fX A
  rw [← hφ] at h
  set e := h.isColimit.coconePointUniqueUpToIso (CommRingCat.pushoutCoconeIsColimit k A Γ(X, ⊤))
    with he
  have hinl : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop) ≫ e.hom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤)))
        := by
    have := h.isColimit.comp_coconePointUniqueUpToIso_hom (CommRingCat.pushoutCoconeIsColimit k A
      Γ(X, ⊤))
      WalkingSpan.left
    rw [← CommRingCat.pushoutCocone_inl]
    exact this
  have hincl : Function.Bijective (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B :=
    Γ(X, ⊤))) := by
    have heq : ∀ a : A, Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤)) a
      =
        e.hom.hom (((pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := by
      intro a
      have := congrArg (fun f => (CommRingCat.Hom.hom f) a) hinl
      exact this.symm
    have hfun : (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤)) : A → A
      ⊗[k] Γ(X, ⊤)) =
        e.hom.hom ∘ (fun a => ((pullback.snd fX (Spec.map (CommRingCat.ofHom (algebraMap k
          A)))).appTop).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) := funext heq
    rw [hfun]
    refine e.commRingCatIsoToRingEquiv.bijective.comp ?_
    have hA' := hA
    simp only [CommRingCat.hom_comp, RingHom.coe_comp] at hA'
    exact hA'
  have hl : Function.Bijective (LinearMap.lTensor A (Algebra.linearMap k Γ(X, ⊤))) := by
    have heq : (LinearMap.lTensor A (Algebra.linearMap k Γ(X, ⊤)) : A ⊗[k] k → A ⊗[k] Γ(X, ⊤)) =
        (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := A) (B := Γ(X, ⊤))) ∘
          (TensorProduct.rid k A) := by
      apply funext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a c =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply,
          TensorProduct.rid_tmul,
          Algebra.TensorProduct.includeLeftRingHom_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      | add x y hx hy => simp only [map_add, Function.comp_apply] at hx hy ⊢; rw [hx, hy]
    rw [heq]
    exact hincl.comp (TensorProduct.rid k A).bijective
  have hφbij := (Module.FaithfullyFlat.lTensor_bijective_iff_bijective k A (Algebra.linearMap k
    Γ(X, ⊤))).mp hl
  exact hφbij
end bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
