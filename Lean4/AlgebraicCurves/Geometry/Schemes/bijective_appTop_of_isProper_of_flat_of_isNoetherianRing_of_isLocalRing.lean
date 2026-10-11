/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.Algebraize
import AlgebraicCurves.Foundations.CommutativeAlgebra.AdicCompletionLocalRing
import AlgebraicCurves.Foundations.CommutativeAlgebra.AdicCompletion_isNoetherianRing_of_isNoetherianRing
import AlgebraicCurves.Geometry.Schemes.bijective_appTop_of_isProper_of_flat_of_isAdicComplete

/-!
# bijective app Top of is Proper of flat of is Noetherian Ring of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace TensorProduct

universe u

noncomputable section

namespace SolH0Nloc

lemma bijective_of_isPushout_of_faithfullyFlat {R S B P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ B}
    {inl : S ⟶ P} {inr : B ⟶ P} (H : IsPushout f g inl inr)
    (hg : g.hom.FaithfullyFlat)
    (hinr : Function.Bijective inr) : Function.Bijective f := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, (f ≫ inl).hom]
  have hgff : Module.FaithfullyFlat R B := hg
  have : IsScalarTower R S P := IsScalarTower.of_algebraMap_eq fun r => rfl
  have : IsScalarTower R B P := IsScalarTower.of_algebraMap_eq fun r => by
    change (f ≫ inl).hom r = (g ≫ inr).hom r
    rw [H.w]
  have H' : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap S P)) (CommRingCat.ofHom (algebraMap B P)) := H
  have hP : Algebra.IsPushout R S B P := CommRingCat.isPushout_iff_isPushout.mp H'
  have hP' : Algebra.IsPushout R B S P := hP.symm
  let e : B ⊗[R] S ≃ₐ[B] P := Algebra.IsPushout.equiv R B S P
  let fl : R →ₗ[R] S := (Algebra.ofId R S).toLinearMap
  have hcomp : ∀ b : B, e (fl.lTensor B ((TensorProduct.rid R B).symm b)) = algebraMap B P b := by
    intro b
    simp only [TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, fl, AlgHom.toLinearMap_apply,
      map_one]
    rw [Algebra.IsPushout.equiv_tmul, map_one, mul_one]
  have hbij : Function.Bijective (fl.lTensor B) := by
    have h2 : Function.Bijective (fun b : B => e (fl.lTensor B ((TensorProduct.rid R B).symm b)))
      := by
      simp_rw [hcomp]; exact hinr
    have h3 : (fun b : B => e (fl.lTensor B ((TensorProduct.rid R B).symm b))) =
        e ∘ (fl.lTensor B) ∘ (TensorProduct.rid R B).symm := rfl
    rw [h3] at h2
    have h4 := (Function.Bijective.of_comp_iff' e.bijective _).mp h2
    exact (Function.Bijective.of_comp_iff _ (TensorProduct.rid R B).symm.bijective).mp h4
  have := (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R B fl).mp hbij
  exact this

section Completion

variable (A : CommRingCat.{u}) [IsNoetherianRing A] [IsLocalRing A]

/-- The completion of the local ring with respect to its maximal ideal. -/
abbrev Ahat : Type u := AdicCompletion (IsLocalRing.maximalIdeal A) A

scoped instance : IsNoetherianRing (Ahat A) := AdicCompletion.isNoetherianRing_of_isNoetherianRing _

scoped instance : IsAdicComplete (IsLocalRing.maximalIdeal (Ahat A)) (Ahat A) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal A) (Ahat A)).mpr
    (AdicCompletion.isAdicComplete AdicCompletion.maximalIdeal_fg)

scoped instance : Module.FaithfullyFlat A (Ahat A) := by
  refine ⟨fun m hm => ?_⟩
  have hm' : m = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  subst hm'
  rw [Ideal.smul_top_eq_map, ← AdicCompletion.maximalIdeal_eq_map]
  intro h
  have : (1 : Ahat A) ∈ (IsLocalRing.maximalIdeal (Ahat A)).restrictScalars A := by
    rw [h]; trivial
  exact (IsLocalRing.maximalIdeal.isMaximal (Ahat A)).ne_top
    ((Ideal.eq_top_iff_one _).mpr this)

/-- The induced homomorphism from the residue field to the residue field of the completion. -/
def resMap : A ⧸ IsLocalRing.maximalIdeal A →+* Ahat A ⧸ IsLocalRing.maximalIdeal (Ahat A) :=
  Ideal.quotientMap _ (algebraMap A (Ahat A)) (by
    rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.le_comap_map)

lemma resMap_bijective : Function.Bijective (resMap A) := by
  constructor
  · refine Ideal.quotientMap_injective' (fun x hx => ?_)
    rw [Ideal.mem_comap] at hx
    by_contra hx'
    have hu : IsUnit x := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hx'
    exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu.map _)
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (IsLocalRing.maximalIdeal A)
      AdicCompletion.maximalIdeal_fg 1 x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    simp only [resMap, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq]
    have : y ∈ IsLocalRing.maximalIdeal (Ahat A) := by
      rw [AdicCompletion.maximalIdeal_eq_map]; rwa [pow_one] at hy
    simpa using neg_mem this

/-- The isomorphism identifying the residue field with that of the completed local ring. -/
def resIso : CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A) ≅
    CommRingCat.of (Ahat A ⧸ IsLocalRing.maximalIdeal (Ahat A)) :=
  (RingEquiv.ofBijective (resMap A) (resMap_bijective A)).toCommRingCatIso

lemma quot_comp_resIso :
    CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) ≫ (resIso A).hom =
      CommRingCat.ofHom (algebraMap A (Ahat A)) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Ahat A))) := by
  ext a; rfl

end Completion

lemma appTop_bijective_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f.appTop :=
  (asIso (f.app ⊤)).commRingCatIsoToRingEquiv.bijective

lemma appLE_top_top' {Y Z : Scheme.{u}} (f : Y ⟶ Z) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  f.appLE_eq_app

section BaseChange

variable {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
  (p : X ⟶ Spec A) [IsProper p] [Flat p]

/-- The spectrum morphism induced by the map into the adic completion. -/
abbrev jA : Spec (CommRingCat.of (Ahat A)) ⟶ Spec A := Spec.map (CommRingCat.ofHom (algebraMap A
  (Ahat A)))

/-- The base change of the scheme to the completed local ring. -/
abbrev Xh : Scheme.{u} := pullback p (jA (A := A))

/-- The structure morphism of the base change to the completed local ring. -/
abbrev ph : Xh p ⟶ Spec (CommRingCat.of (Ahat A)) := pullback.snd _ _

/-- The projection from the completed base change to the original scheme. -/
abbrev gh : Xh p ⟶ X := pullback.fst _ _

scoped instance : IsProper (ph p) := inferInstance

scoped instance : Flat (jA (A := A)) := by
  rw [Flat.SpecMap_iff]
  change (algebraMap A (Ahat A)).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

omit [IsProper p] [Flat p] in
lemma closedFibre_bijective
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective (pullback.snd (ph p) (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Ahat A)))))).appTop := by
  set qA := CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) with hqA
  set qh := CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Ahat A))) with hqh
  set jj := CommRingCat.ofHom (algebraMap A (Ahat A)) with hjj
  let e₁ : pullback (ph p) (Spec.map qh) ≅ pullback p (Spec.map qh ≫ jA (A := A)) :=
    pullbackLeftPullbackSndIso p (jA (A := A)) (Spec.map qh)
  have hcomp : Spec.map qh ≫ jA (A := A) = Spec.map (resIso A).hom ≫ Spec.map qA := by
    rw [← Spec.map_comp, ← Spec.map_comp, quot_comp_resIso]
  let m : pullback p (Spec.map qh ≫ jA (A := A)) ⟶ pullback p (Spec.map qA) :=
    pullback.map _ _ _ _ (𝟙 X) (Spec.map (resIso A).hom) (𝟙 _) (by simp) (by rw [hcomp]; simp)
  have hm : IsIso m := by dsimp only [m]; infer_instance
  have hm2 : m ≫ pullback.snd p (Spec.map qA) = pullback.snd _ _ ≫ Spec.map (resIso A).hom :=
    pullback.lift_snd _ _ _
  have he₁ : e₁.hom ≫ pullback.snd p (Spec.map qh ≫ jA (A := A)) = pullback.snd (ph p) (Spec.map
    qh) :=
    pullbackLeftPullbackSndIso_hom_snd _ _ _
  have h1 : Function.Bijective (pullback.snd p (Spec.map qh ≫ jA (A := A))).appTop := by
    have e2 : (Spec.map (resIso A).hom).appTop ≫ (pullback.snd p (Spec.map qh ≫ jA (A := A))).appTop
        = (pullback.snd p (Spec.map qA)).appTop ≫ m.appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hm2]
    have hb1 : Function.Bijective ((pullback.snd p (Spec.map qA)).appTop ≫ m.appTop) := by
      change Function.Bijective (m.appTop.hom ∘ (pullback.snd p (Spec.map qA)).appTop.hom)
      have := hm
      exact (appTop_bijective_of_isIso m).comp h
    rw [← e2] at hb1
    change Function.Bijective ((pullback.snd p (Spec.map qh ≫ jA (A := A))).appTop.hom ∘
      (Spec.map (resIso A).hom).appTop.hom) at hb1
    exact (Function.Bijective.of_comp_iff _
      (appTop_bijective_of_isIso (Spec.map (resIso A).hom))).mp hb1
  rw [← he₁, Scheme.Hom.comp_appTop]
  change Function.Bijective (e₁.hom.appTop.hom ∘ (pullback.snd p (Spec.map qh ≫ jA (A :=
    A))).appTop.hom)
  exact (appTop_bijective_of_isIso e₁.hom).comp h1
omit [Flat p] in
lemma isPushout_appTop :
    IsPushout p.appTop (jA (A := A)).appTop (gh p).appTop (ph p).appTop := by
  have H : IsPullback (gh p) (ph p) p (jA (A := A)) := IsPullback.of_hasPullback _ _
  have hUY : (⊤ : (Xh p).Opens) = (gh p) ⁻¹ᵁ ⊤ ⊓ (ph p) ⁻¹ᵁ ⊤ := by simp
  have : CompactSpace X := (quasiCompact_iff_compactSpace p).mp inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hc : IsCompact ((⊤ : X.Opens) : Set X) := by simpa using isCompact_univ
  have hqs : IsQuasiSeparated ((⊤ : X.Opens) : Set X) := by simpa using isQuasiSeparated_univ
  have h1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤)
    le_top le_top hUY (isAffineOpen_top _) (isAffineOpen_top _) hc hqs
  have h2 := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := ⊤) le_top le_top hUY).mp h1
  rw [appLE_top_top', appLE_top_top', appLE_top_top', appLE_top_top'] at h2
  exact h2

lemma jA_appTop_faithfullyFlat : (jA (A := A)).appTop.hom.FaithfullyFlat := by
  have e : (jA (A := A)).appTop = (Scheme.ΓSpecIso A).hom ≫
      CommRingCat.ofHom (algebraMap A (Ahat A)) ≫ (Scheme.ΓSpecIso (.of (Ahat A))).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [e]
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  refine RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.bijective) ?_
  refine RingHom.FaithfullyFlat.stableUnderComposition _ _ ?_
    (RingHom.FaithfullyFlat.of_bijective
      (Scheme.ΓSpecIso (.of (Ahat A))).symm.commRingCatIsoToRingEquiv.bijective)
  exact (RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance

theorem main
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop := by
  have hh := closedFibre_bijective p h
  have hC1 : Function.Bijective (ph p).appTop :=
    AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isAdicComplete (ph p) hh
  exact bijective_of_isPushout_of_faithfullyFlat (isPushout_appTop p) (jA_appTop_faithfullyFlat (A
    := A)) hC1

end BaseChange

end SolH0Nloc

open Lean Elab Command in
run_cmd
  for word in ([
      ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
        "bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing." ++
        "SolH0Nloc")
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


end

open Lean Elab Command in
run_cmd
  for word in ([
      ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
        "bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing." ++
        "SolH0Nloc")
    ] : List String) do
    let ns := word.toName
    for ext in (← scopedEnvExtensionsRef.get) do
      modifyEnv fun env =>
        let st := ext.ext.getState env
        match st.stateStack with
        | top :: stack =>
          let top := { top with activeScopes := top.activeScopes.erase ns }
          ext.activateScoped (ext.ext.setState env { st with stateStack := top :: stack }) ns
        | _ => env


theorem
  _root_.AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop :=
  SolH0Nloc.main p h
end bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation

attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
