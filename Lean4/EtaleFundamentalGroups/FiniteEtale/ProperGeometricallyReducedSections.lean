/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Affine.FlatBaseChangeAffinization
import SchemeTheory.FiniteEtale.Algebra.FiniteGeometricallyReducedEtale
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.Algebra.Category.Ring.Constructions
import AlgebraicCurves.Geometry.Schemes.finite_appTop_of_isProper_of_isNoetherianRing

/-!
# Global sections of proper geometrically reduced schemes over fields

The global section algebra is finite by proper coherent cohomology. Its
extension to an algebraic closure is reduced because flat base change
identifies it with the actual sections of the reduced geometric fibre.
The resulting finite étale algebra is the field case of the supplier
needed for Stacks Project Tag 0BUN.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- The actual global-section map of a proper geometrically reduced scheme
over a field is finite étale. -/
theorem finite_etale_appTop_of_isProper_of_geometricallyReduced_overField
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f] [GeometricallyReduced f] :
    f.appTop.hom.Finite ∧ f.appTop.hom.Etale := by
  have hFinite : f.appTop.hom.Finite :=
    finite_appTop_of_isProper_of_isNoetherianRing f
  refine ⟨hFinite, ?_⟩
  let scalarMap : K →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom
  let : Algebra K Γ(X, ⊤) := scalarMap.toAlgebra
  have : Module.Finite K Γ(X, ⊤) :=
    hFinite.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  let Kbar : Type u := AlgebraicClosure K
  let g : Spec (CommRingCat.of Kbar) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Kbar))
  have hReduced : IsReduced (pullback f g) :=
    GeometricallyReduced.geometrically_isReduced (f := f) g _ _
      (IsPullback.of_hasPullback f g)
  have hPushout : IsPushout
      (CommRingCat.ofHom (algebraMap K Kbar)) (CommRingCat.ofHom scalarMap)
      ((Scheme.ΓSpecIso (CommRingCat.of Kbar)).inv ≫ (pullback.snd f g).appTop)
      (pullback.fst f g).appTop := by
    refine (isPushout_appTop_of_flat f g).flip.of_iso
      (Scheme.ΓSpecIso (CommRingCat.of K))
      (Scheme.ΓSpecIso (CommRingCat.of Kbar)) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K Kbar))
    · change f.appTop ≫ 𝟙 _ =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop)
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
    · change (pullback.snd f g).appTop ≫ 𝟙 _ =
        (Scheme.ΓSpecIso (CommRingCat.of Kbar)).hom ≫
          ((Scheme.ΓSpecIso (CommRingCat.of Kbar)).inv ≫ (pullback.snd f g).appTop)
      rw [Iso.hom_inv_id_assoc, Category.comp_id]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  let e : Kbar ⊗[K] Γ(X, ⊤) ≃+* Γ(pullback f g, ⊤) :=
    ((CommRingCat.isPushout_tensorProduct K Kbar Γ(X, ⊤)).isoPushout ≪≫
      hPushout.isoPushout.symm).commRingCatIsoToRingEquiv
  have : _root_.IsReduced (Kbar ⊗[K] Γ(X, ⊤)) :=
    isReduced_of_injective e.toRingHom e.injective
  have hEtale : Algebra.Etale K Γ(X, ⊤) :=
    Algebra.etale_of_finite_of_isReduced_algebraicClosure_tensorProduct K Γ(X, ⊤)
  exact (RingHom.Etale.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv f.appTop).mp hEtale

end AlgebraicGeometry
