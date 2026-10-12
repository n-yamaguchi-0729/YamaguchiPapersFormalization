/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.Ext
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_baseChange
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_tensorPow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_tensorPow_iso

/-!
# Fibrewise algebraic triviality over a discrete valuation ring

The closed fibre and the generic Poincare comparison give algebraic triviality on every fibre.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ClosedFibreZero

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.SmoothProperCurve

namespace GlueKit

theorem isAlgEquivZero_fibre_of_isPullback {B B' X X' : Scheme.{u}} (x : X ⟶ B) (t : B' ⟶ B)
    (x' : X' ⟶ B') (g : X' ⟶ X)
    (H : IsPullback g x' x t) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ B') (N :
      X.Modules)
    (h : IsAlgEquivZero (pullback.snd x' s) ((Scheme.Modules.pullback (pullback.fst x' s)).obj
      ((Scheme.Modules.pullback g).obj N))) :
    IsAlgEquivZero (pullback.snd x (s ≫ t)) ((Scheme.Modules.pullback (pullback.fst x (s ≫ t))).obj
      N) := by
  let ℓ : pullback x (s ≫ t) ⟶ X' :=
    H.lift (pullback.fst x (s ≫ t)) (pullback.snd x (s ≫ t) ≫ s)
      (by rw [pullback.condition, Category.assoc])
  have hℓ₁ : ℓ ≫ g = pullback.fst x (s ≫ t) := H.lift_fst _ _ _
  have hℓ₂ : ℓ ≫ x' = pullback.snd x (s ≫ t) ≫ s := H.lift_snd _ _ _
  let e : pullback x (s ≫ t) ⟶ pullback x' s := pullback.lift ℓ (pullback.snd x (s ≫ t)) hℓ₂
  have he : e ≫ pullback.snd x' s = pullback.snd x (s ≫ t) := pullback.lift_snd _ _ _
  have hefst : e ≫ pullback.fst x' s ≫ g = pullback.fst x (s ≫ t) := by
    rw [← Category.assoc, pullback.lift_fst, hℓ₁]
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp e (pullback.fst x' s)).app _ ≪≫
    (Scheme.Modules.pullbackComp (e ≫ pullback.fst x' s) g).app N ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc, hefst])).app N

theorem ker_eq_bot_or_eq_maximalIdeal {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    {k : Type*} [Field k] (σ : O →+* k) : RingHom.ker σ = ⊥ ∨ RingHom.ker σ =
      IsLocalRing.maximalIdeal O := by
  by_cases h : RingHom.ker σ = ⊥
  · exact Or.inl h
  · right
    have : (RingHom.ker σ).IsPrime := RingHom.ker_isPrime σ
    have : (RingHom.ker σ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance h
    exact IsLocalRing.eq_maximalIdeal inferInstance

theorem exists_comp_eq_of_ker_le {O k k' : Type*} [CommRing O] [CommRing k] [CommRing k']
    (π : O →+* k) (hπ : Function.Surjective π)
    (σ : O →+* k') (h : RingHom.ker π ≤ RingHom.ker σ) : ∃ τ : k →+* k', τ.comp π = σ := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) σ (fun a ha => h ha)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply]
  have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a
    := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.apply_symm_apply, RingHom.quotientKerEquivOfSurjective_apply_mk]
  rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
  rfl

theorem isAlgEquivZero_snd_comp_of_fibreAt {R : Type u} [CommRing R] {C T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (L :
      (pullback c t).Modules)
    (h : IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t)
      s)).obj L)) :
    IsAlgEquivZero (pullback.snd c (s ≫ t)) ((Scheme.Modules.pullback (mapOnProdOver c s (rfl : s ≫
      t = s ≫ t))).obj L) := by
  let e : pullback c (s ≫ t) ⟶ pullback (pullback.snd c t) s :=
    pullback.lift (mapOnProdOver c s rfl) (pullback.snd c (s ≫ t)) (mapOnProdOver_snd c s rfl)
  have he : e ≫ fibreAt c t s = pullback.snd c (s ≫ t) := pullback.lift_snd _ _ _
  have hefst : e ≫ pullback.fst (pullback.snd c t) s = mapOnProdOver c s rfl := pullback.lift_fst _
    _ _
  refine IsAlgEquivZero.of_iso ?_ (h.pullback e he)
  exact (Scheme.Modules.pullbackComp e (pullback.fst (pullback.snd c t) s)).app L ≪≫
    (Scheme.Modules.pullbackCongr hefst).app L

end GlueKit

namespace GenericLeg

theorem isAlgEquivZero_fibre_of_factor
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t)
    (N' : (pullback c t').Modules)
    (hN' : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s' : Spec (CommRingCat.of k) ⟶ T'),
      IsAlgEquivZero (fibreAt c t' s') ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t')
        s')).obj N'))
    (e : (M.pullbackAlong ψ).L ≅ N')
    (k : Type u) [Field k] [IsAlgClosed k] (s' : Spec (CommRingCat.of k) ⟶ T')
    (s : Spec (CommRingCat.of k) ⟶ T) (hs : s = s' ≫ ψ.1) :
    IsAlgEquivZero (fibreAt c t s) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t)
      s)).obj M.L) := by
  subst hs
  have hm : (pullback.fst (pullback.snd c t) (s' ≫ ψ.1) ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) (s' ≫ ψ.1) ≫ s') ≫ t' := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
      Category.assoc, ψ.2,
      Category.assoc]
  let m : pullback (pullback.snd c t) (s' ≫ ψ.1) ⟶ pullback c t' :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst c t) (pullback.snd _ _ ≫ s') hm
  have hm2 : m ≫ pullback.snd c t' = pullback.snd (pullback.snd c t) (s' ≫ ψ.1) ≫ s' :=
    pullback.lift_snd _ _ _
  let eA : pullback (pullback.snd c t) (s' ≫ ψ.1) ⟶ pullback (pullback.snd c t') s' :=
    pullback.lift m (pullback.snd _ _) hm2
  have heA : eA ≫ fibreAt c t' s' = fibreAt c t (s' ≫ ψ.1) := by
    change eA ≫ pullback.snd _ _ = pullback.snd _ _
    exact pullback.lift_snd _ _ _
  have hbcs : m ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) (s' ≫ ψ.1) := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      rw [show baseChangeSnd c ψ ≫ pullback.fst c t = pullback.fst c t' from
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc]
      rw [show baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 from
        pullback.lift_snd _ _ _,
        ← Category.assoc, hm2, Category.assoc, pullback.condition]
  have hcomp : eA ≫ pullback.fst (pullback.snd c t') s' ≫ baseChangeSnd c ψ = pullback.fst
    (pullback.snd c t) (s' ≫ ψ.1) := by
    rw [← Category.assoc,
      show eA ≫ pullback.fst (pullback.snd c t') s' = m from pullback.lift_fst _ _ _, hbcs]
  have h1 : IsAlgEquivZero (fibreAt c t' s')
      ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t') s')).obj (M.pullbackAlong ψ).L) :=
    (hN' k s').of_iso ((Scheme.Modules.pullback _).mapIso e.symm)
  have h2 := h1.pullback eA heA
  refine h2.of_iso ?_
  exact (Scheme.Modules.pullback eA).mapIso ((Scheme.Modules.pullbackComp (pullback.fst
    (pullback.snd c t') s') (baseChangeSnd c ψ)).app M.L) ≪≫
    (Scheme.Modules.pullbackComp eA _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L

end GenericLeg

end JacobianVarieties.Picard.Proofs.ClosedFibreZero

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.JacobianVarieties.Picard.Proofs.ClosedFibreZero in
theorem
fibrewiseAlgEquivZero_of_isAlgEquivZero_pullback_closedFibre_of_pullbackAlong_iso_tensorPow_poincare
    {A : Type u} [CommRing A] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of A))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) c)
    (D : RelativePic0Designation A c) (hrep : Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c
      ε) D))
    (k : Type u) [Field k] [Algebra A k]
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : A →+* O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k) (htoκs : Function.Surjective toκ)
    (bc : pullback c (specMap A k) ⟶ pullback c (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
    (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) D.toBase) (n : ℕ)
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom ρO)))
    (hclosed : IsAlgEquivZero (pullback.snd c (specMap A k)) ((Scheme.Modules.pullback bc).obj M.L))
    (hgen : Nonempty ((M.pullbackAlong
        (⟨Spec.map (CommRingCat.ofHom (algebraMap O T')),
          by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) (Spec.map
            (CommRingCat.ofHom ρO)))).L ≅
      (hrep.some.poincare.pullbackAlong y).L.tensorPow n)) :
    FibrewiseAlgEquivZero M := by
  classical
  intro k' _ _ s
  let tO : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom ρO)
  let gT : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) tO :=
    ⟨Spec.map (CommRingCat.ofHom (algebraMap O T')),
      by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : CommRingCat.of O ⟶ CommRingCat.of k', s = Spec.map σ := ⟨Spec.preimage s,
    (Spec.map_preimage s).symm⟩
  rcases GlueKit.ker_eq_bot_or_eq_maximalIdeal σ.hom with hker | hker
  · have hinj : Function.Injective σ.hom := (RingHom.injective_iff_ker_eq_bot _).mpr hker
    let σ' : T' →+* k' := IsFractionRing.lift hinj
    have hσ : σ = CommRingCat.ofHom (σ'.comp (algebraMap O T')) := by
      ext x
      exact (IsFractionRing.lift_algebraMap hinj x).symm
    have hs : Spec.map σ = Spec.map (CommRingCat.ofHom σ') ≫ gT.1 := by
      rw [hσ, CommRingCat.ofHom_comp, Spec.map_comp]
    have hP : FibrewiseAlgEquivZero hrep.some.poincare := hrep.some.poincare_mem
    have hPy : FibrewiseAlgEquivZero (hrep.some.poincare.pullbackAlong y) := hP.pullback y
    have hN' : ∀ (k₁ : Type u) [Field k₁] [IsAlgClosed k₁] (s' : Spec (CommRingCat.of k₁) ⟶ Spec
      (CommRingCat.of T')),
        IsAlgEquivZero (fibreAt c (Spec.map (CommRingCat.ofHom ((algebraMap O T').comp ρO))) s')
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd c _) s')).obj
            ((hrep.some.poincare.pullbackAlong y).L.tensorPow n)) := by
      intro k₁ _ _ s'
      exact ((hPy k₁ s').tensorPow n).of_iso
        (AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso _ _ n).some.symm
    exact GenericLeg.isAlgEquivZero_fibre_of_factor c gT M _ hN' hgen.some k' (Spec.map
      (CommRingCat.ofHom σ')) (Spec.map σ) hs
  · have hkert : RingHom.ker toκ = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ htoκs)
    obtain ⟨τ, hτ⟩ := GlueKit.exists_comp_eq_of_ker_le toκ htoκs σ.hom (by rw [hkert, hker])
    have hs : Spec.map σ = Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom toκ) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτ]; rfl
    have hspec : Spec.map (CommRingCat.ofHom toκ) ≫ tO = specMap A k := by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, htoκ]
    have H : IsPullback bc (pullback.snd c (specMap A k)) (pullback.snd c tO) (Spec.map
      (CommRingCat.ofHom toκ)) := by
      refine IsPullback.of_right (h₁₂ := pullback.fst c tO) (v₁₃ := c) (h₂₂ := tO) ?_ hbc₂
        (IsPullback.of_hasPullback c tO)
      rw [hbc₁, hspec]
      exact IsPullback.of_hasPullback c (specMap A k)
    let : Algebra k k' := τ.toAlgebra
    have hbc' := AlgebraicGeometry.RelPicard.IsAlgEquivZero.baseChange k' (pullback.snd c (specMap
      A k)) hclosed
    have key := GlueKit.isAlgEquivZero_fibre_of_isPullback (pullback.snd c tO) (Spec.map
      (CommRingCat.ofHom toκ))
      (pullback.snd c (specMap A k)) bc H (Spec.map (CommRingCat.ofHom (algebraMap k k'))) M.L hbc'
    have : ∀ s'' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of O),
        s'' = Spec.map (CommRingCat.ofHom (algebraMap k k')) ≫ Spec.map (CommRingCat.ofHom toκ) →
        IsAlgEquivZero (fibreAt c tO s'') ((Scheme.Modules.pullback (pullback.fst (pullback.snd c
          tO) s'')).obj M.L) := by
      rintro _ rfl; exact key
    exact this _ hs
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
