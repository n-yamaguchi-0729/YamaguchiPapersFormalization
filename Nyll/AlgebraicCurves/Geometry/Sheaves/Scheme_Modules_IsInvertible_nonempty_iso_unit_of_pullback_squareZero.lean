/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTildePullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Projective_nonempty_linearEquiv_of_baseChange_quotient_of_squareZero

/-!
# Triviality of an invertible module across a square-zero thickening

An invertible module on an affine scheme is trivial when its pullback to a square-zero
quotient is trivial.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

private theorem proj_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (M : Type u) [AddCommGroup M] [Module S M] [Module.Projective S M] :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.Projective R M := by
  let : Module R M := Module.compHom M e.toRingHom
  have : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.of_ringEquiv e.symm
  have : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  have slEq : M ≃ₛₗ[(e.symm : S →+* R)] M :=
    { toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl,
      map_smul' := fun s m => by
        simp only [id]
        change s • m = (e (e.symm s)) • m
        rw [e.apply_symm_apply] }
  exact Module.Projective.of_equiv slEq

private theorem fin_of_surj {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : Type u) [AddCommGroup M] [Module S M]
    [Module.Finite S M] :
    letI : Module R M := Module.compHom M f
    Module.Finite R M := by
  let : Module R M := Module.compHom M f
  obtain ⟨s, hs⟩ := ‹Module.Finite S M›.1
  refine ⟨s, ?_⟩
  rw [eq_top_iff]; intro m _
  have hm : m ∈ Submodule.span S (↑s : Set M) := hs ▸ Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
  · intro x hx; exact Submodule.subset_span hx
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    obtain ⟨r, hr⟩ := hf a
    have heq : a • x = r • x := by
      change a • x = f r • x; rw [hr]
    rw [heq]; exact Submodule.smul_mem _ r hx

theorem
    _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (L : (Spec (CommRingCat.of B)).Modules) (hL : Scheme.Modules.IsInvertible L)
    (h : Nonempty ((Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj L
          ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf)) :
    Nonempty (L ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  have hIso := Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial
    (R := CommRingCat.of B) L hL.exists_trivialization
  let eL := @asIso _ _ _ _ _ hIso
  have hPtop := Scheme.Modules.projective_sections_of_locallyTrivial (X := Spec (.of B)) L
    hL.exists_trivialization ⟨⊤, isAffineOpen_top _⟩
  have hFtop := Scheme.Modules.finite_sections_of_locallyTrivial (X := Spec (.of B)) L
    hL.exists_trivialization ⟨⊤, isAffineOpen_top _⟩
  let gsi : B ≃+* ↑Γ(Spec (CommRingCat.of B), (⊤ : (Spec (.of B)).Opens)) :=
    (StructureSheaf.globalSectionsIso B).commRingCatIsoToRingEquiv
  have hQproj : Module.Projective B
      ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
    have := proj_of_ringEquiv gsi (↑Γ(L, (⊤ : (Spec (.of B)).Opens)))
    exact this
  have hQfin : Module.Finite B
      ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L) := by
    have := fin_of_surj gsi.toRingHom gsi.surjective (↑Γ(L, (⊤ : (Spec (.of B)).Opens)))
    exact this
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have e5 :=
    (tilde.pullbackSpecIso φ ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L)).symm ≪≫
    (Scheme.Modules.pullback (Spec.map φ)).mapIso eL ≪≫
    h.some ≪≫
    (tildeSelf (R := CommRingCat.of (B ⧸ I))).symm
  have e6 := (tilde.fullyFaithfulFunctor (R := CommRingCat.of (B ⧸ I))).preimageIso e5
  let e7 : ((B ⧸ I) ⊗[B] ↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L))
      ≃ₗ[B ⧸ I] (B ⧸ I) ⊗[B] B :=
    e6.toLinearEquiv.trans (TensorProduct.AlgebraTensorModule.rid B (B ⧸ I) (B ⧸ I)).symm
  obtain ⟨eQB⟩ := Module.Projective.nonempty_linearEquiv_of_baseChange_quotient_of_squareZero
    I hI (↑((moduleSpecΓFunctor (R := CommRingCat.of B)).obj L)) B e7
  exact ⟨eL.symm ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso (LinearEquiv.toModuleIso eQB) ≪≫
    tildeSelf (R := CommRingCat.of B)⟩

end
end Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
