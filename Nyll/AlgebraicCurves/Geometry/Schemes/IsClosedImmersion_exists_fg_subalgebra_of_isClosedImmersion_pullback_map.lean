/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Command
import Nyll.AlgebraicCurves.Geometry.Schemes.exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback
import Nyll.AlgebraicCurves.Foundations.Algebra.Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map

/-!
# Is Closed Immersion exists fg subalgebra of is Closed Immersion pullback map
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
attribute [-instance] AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
attribute [-simp] AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace CIDescGC6

section GammaBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X₀ X₁ : Scheme.{u}} [IsAffine X₀] (x₀ : X₀ ⟶ Spec (CommRingCat.of R))
  (a : X₁ ⟶ X₀) (b : X₁ ⟶ Spec (CommRingCat.of S))
  (H : IsPullback a b x₀ (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  [Algebra R Γ(X₀, ⊤)]
  (halg : algebraMap R Γ(X₀, ⊤) =
    (Scheme.Hom.appTop x₀).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

include H halg in
theorem exists_ringEquiv_tmul :
    ∃ e : S ⊗[R] Γ(X₀, ⊤) ≃+* Γ(X₁, ⊤), ∀ (s : S) (c : Γ(X₀, ⊤)),
      e (s ⊗ₜ c) = b.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) * a.appTop.hom c
        := by
  have hpo := isPushout_appTop_of_isPullback H
  let iS : Algebra S Γ(X₁, ⊤) :=
    (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra
  let i01 : Algebra Γ(X₀, ⊤) Γ(X₁, ⊤) := a.appTop.hom.toAlgebra
  let iR : Algebra R Γ(X₁, ⊤) :=
    ((algebraMap Γ(X₀, ⊤) Γ(X₁, ⊤)).comp (algebraMap R Γ(X₀, ⊤))).toAlgebra
  have : IsScalarTower R Γ(X₀, ⊤) Γ(X₁, ⊤) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hnat : ∀ r : R, (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S r) =
      (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := fun r => by
    have n1 := congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S)))
    dsimp only at n1
    rwa [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply,
      CommRingCat.hom_ofHom] at n1
  have hsq : ∀ r : R, algebraMap R Γ(X₁, ⊤) r = algebraMap S Γ(X₁, ⊤) (algebraMap R S r) := by
    intro r
    change a.appTop.hom (algebraMap R Γ(X₀, ⊤) r) =
      b.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S r))
    rw [halg, hnat, RingHom.comp_apply]
    change ((x₀.appTop ≫ a.appTop).hom) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (((Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop ≫ b.appTop).hom)
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
    rw [hpo.w]
  have : IsScalarTower R S Γ(X₁, ⊤) := IsScalarTower.of_algebraMap_eq hsq
  have commf : x₀.appTop ≫ (Iso.refl _).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R Γ(X₀, ⊤)) := by
    rw [halg, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
      Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  have commg : (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
        (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom (algebraMap R S) :=
    Scheme.ΓSpecIso_naturality _
  have comminl : a.appTop ≫ (Iso.refl _).hom =
      (Iso.refl _).hom ≫ CommRingCat.ofHom (algebraMap Γ(X₀, ⊤) Γ(X₁, ⊤)) := by
    change a.appTop ≫ 𝟙 _ = 𝟙 _ ≫ CommRingCat.ofHom a.appTop.hom
    rw [Category.comp_id, Category.id_comp, CommRingCat.ofHom_hom]
  have comminr : b.appTop ≫ (Iso.refl _).hom =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom (algebraMap S Γ(X₁, ⊤)) := by
    change b.appTop ≫ 𝟙 _ = (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫
      CommRingCat.ofHom (b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
    rw [Category.comp_id, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
      Iso.hom_inv_id_assoc]
  have hpo' : IsPushout (CommRingCat.ofHom (algebraMap R Γ(X₀, ⊤))) (CommRingCat.ofHom (algebraMap
    R S))
      (CommRingCat.ofHom (algebraMap Γ(X₀, ⊤) Γ(X₁, ⊤))) (CommRingCat.ofHom (algebraMap S Γ(X₁,
        ⊤))) :=
    hpo.of_iso (Scheme.ΓSpecIso (CommRingCat.of R)) (Iso.refl _) (Scheme.ΓSpecIso (CommRingCat.of
      S))
      (Iso.refl _) commf commg comminl comminr
  have hA : Algebra.IsPushout R Γ(X₀, ⊤) S Γ(X₁, ⊤) := CommRingCat.isPushout_iff_isPushout.mp hpo'
  have : Algebra.IsPushout R S Γ(X₀, ⊤) Γ(X₁, ⊤) := hA.symm
  refine ⟨(Algebra.IsPushout.equiv R S Γ(X₀, ⊤) Γ(X₁, ⊤)).toRingEquiv, fun s c => ?_⟩
  exact Algebra.IsPushout.equiv_tmul (R := R) (S := S) (R' := Γ(X₀, ⊤)) (S' := Γ(X₁, ⊤)) s c

end GammaBaseChange

theorem surjective_iff_of_tmul {R S D C D₁ C₁ : Type u} [CommRing R] [CommRing S] [CommRing D]
    [CommRing C] [CommRing D₁] [CommRing C₁] [Algebra R S] [Algebra R D] [Algebra R C]
    (φ : D →ₐ[R] C) (eD : S ⊗[R] D ≃+* D₁) (eC : S ⊗[R] C ≃+* C₁)
    (βD : S →+* D₁) (αD : D →+* D₁) (βC : S →+* C₁) (αC : C →+* C₁)
    (heD : ∀ s d, eD (s ⊗ₜ d) = βD s * αD d) (heC : ∀ s c, eC (s ⊗ₜ c) = βC s * αC c)
    (ψ : D₁ →+* C₁) (hβ : ∀ s, ψ (βD s) = βC s) (hα : ∀ d, ψ (αD d) = αC (φ d)) :
    Function.Surjective ψ ↔ Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) φ) := by
  have key : ∀ x, ψ (eD x) = eC (Algebra.TensorProduct.map (AlgHom.id S S) φ x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s d => rw [heD, map_mul, hβ, hα, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, heC]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  constructor
  · intro hψ y
    obtain ⟨x1, hx1⟩ := hψ (eC y)
    obtain ⟨x, rfl⟩ := eD.surjective x1
    rw [key] at hx1
    exact ⟨x, eC.injective hx1⟩
  · intro hφ y
    obtain ⟨z, rfl⟩ := eC.surjective y
    obtain ⟨x, rfl⟩ := hφ z
    exact ⟨eD x, key x⟩

section Stage

/-- The morphism of spectra induced by the algebra structure homomorphism. -/
noncomputable abbrev ι (R₀ S : Type u) [CommRing R₀] [CommRing S] [Algebra R₀ S] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap R₀ S))

noncomputable scoped instance algebraPullback {R₀ : Type u} [CommRing R₀] (S : Type u) [CommRing S]
  [Algebra R₀ S]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R₀)) :
    Algebra S Γ(pullback y (ι R₀ S), ⊤) :=
  ((pullback.snd y (ι R₀ S)).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).toAlgebra

variable {R₀ R : Type u} [CommRing R₀] [CommRing R] [Algebra R₀ R]
  {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of R₀))

/-- The morphism obtained by base changing the original scheme morphism. -/
noncomputable def mBC : pullback (m ≫ v) (ι R₀ R) ⟶ pullback v (ι R₀ R) :=
  (pullbackRightPullbackFstIso v (ι R₀ R) m).inv ≫ pullback.snd m (pullback.fst v (ι R₀ R))

theorem mBC_fst : mBC (R := R) m v ≫ pullback.fst v (ι R₀ R) = pullback.fst (m ≫ v) (ι R₀ R) ≫ m :=
  by
  rw [mBC, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]

theorem mBC_snd : mBC (R := R) m v ≫ pullback.snd v (ι R₀ R) = pullback.snd (m ≫ v) (ι R₀ R) := by
  rw [mBC, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]

scoped instance [LocallyOfFiniteType m] : LocallyOfFiniteType (mBC (R := R) m v) := by
  dsimp only [mBC]; infer_instance

/-- The algebra homomorphism on global sections induced by the base-changed morphism. -/
noncomputable def phi : Γ(pullback v (ι R₀ R), ⊤) →ₐ[R] Γ(pullback (m ≫ v) (ι R₀ R), ⊤) where
  toRingHom := (mBC (R := R) m v).appTop.hom
  commutes' r := by
    change (mBC (R := R) m v).appTop.hom ((pullback.snd v (ι R₀ R)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
        (pullback.snd (m ≫ v) (ι R₀ R)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, mBC_snd]

theorem phi_apply (d : Γ(pullback v (ι R₀ R), ⊤)) : phi (R := R) m v d = (mBC (R := R) m
  v).appTop.hom d := rfl

theorem phi_finiteType [IsAffine V] [IsAffine (pullback (m ≫ v) (ι R₀ R))] [LocallyOfFiniteType m] :
    (phi (R := R) m v).toRingHom.FiniteType :=
  (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
    (inferInstance : LocallyOfFiniteType (mBC (R := R) m v))

theorem stage [IsAffine V] [IsAffine (pullback (m ≫ v) (ι R₀ R))]
    (S : Type u) [CommRing S] [Algebra R₀ S] [Algebra R S] [IsScalarTower R₀ R S]
    (mS : pullback (m ≫ v) (ι R₀ S) ⟶ pullback v (ι R₀ S))
    (h1 : mS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m) (h2 : mS ≫ pullback.snd _ _ = pullback.snd
      _ _) :
    IsAffine (pullback (m ≫ v) (ι R₀ S)) ∧ IsAffine (pullback v (ι R₀ S)) ∧
      (Function.Surjective mS.appTop.hom ↔
        Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) (phi (R := R) m v))) := by
  have hj : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ ι R₀ R = ι R₀ S := by
    rw [ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have sq : ∀ {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R₀)),
      ∃ aY : pullback y (ι R₀ S) ⟶ pullback y (ι R₀ R),
        aY ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        aY ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) ∧
        IsPullback aY (pullback.snd y (ι R₀ S)) (pullback.snd y (ι R₀ R))
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    intro Y y
    refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R S)))
      (by rw [Category.assoc, hj]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    refine IsPullback.of_right (h₁₂ := pullback.fst y (ι R₀ R)) (v₁₃ := y) (h₂₂ := ι R₀ R) ?_
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback y (ι R₀ R))
    rw [pullback.lift_fst, hj]
    exact IsPullback.of_hasPullback y (ι R₀ S)
  obtain ⟨aW, haW1, haW2, HW⟩ := sq (m ≫ v)
  obtain ⟨aV, haV1, haV2, HV⟩ := sq v
  have affW : IsAffine (pullback (m ≫ v) (ι R₀ S)) := IsAffine.of_isPullback HW
  have affV : IsAffine (pullback v (ι R₀ S)) := IsAffine.of_isPullback HV
  obtain ⟨eC, heC⟩ := exists_ringEquiv_tmul (pullback.snd (m ≫ v) (ι R₀ R)) aW (pullback.snd _ (ι
    R₀ S)) HW rfl
  obtain ⟨eD, heD⟩ := exists_ringEquiv_tmul (pullback.snd v (ι R₀ R)) aV (pullback.snd _ (ι R₀ S))
    HV rfl
  refine ⟨affW, affV, ?_⟩
  have heq : mS ≫ aV = aW ≫ mBC (R := R) m v := by
    apply pullback.hom_ext
    · rw [Category.assoc, haV1, h1, Category.assoc, mBC_fst, ← Category.assoc, haW1]
    · rw [Category.assoc, haV2, ← Category.assoc, h2, Category.assoc, mBC_snd, haW2]
  refine surjective_iff_of_tmul (phi (R := R) m v) eD eC (algebraMap S _) aV.appTop.hom (algebraMap
    S _)
    aW.appTop.hom heD heC mS.appTop.hom ?_ ?_
  · intro s
    change mS.appTop.hom ((pullback.snd v (ι R₀ S)).appTop.hom _) = (pullback.snd (m ≫ v) (ι R₀
      S)).appTop.hom _
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, h2]
  · intro d
    rw [phi_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, heq,
      Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

end Stage

end CIDescGC6

open Lean Elab Command in
run_cmd
  for word in ([
      ("AlgebraicCurves.Geometry.Schemes.Proofs." ++
        "IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map." ++
        "CIDescGC6")
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


open CIDescGC6 in
theorem
  _root_.AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of A₀)) [IsAffine V]
    [QuasiCompact m] [QuasiSeparated m] [LocallyOfFiniteType m]
    (hA : ∀ mA : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
        pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mA)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ mT : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ →
        IsClosedImmersion mT := by
  classical
  let mA : pullback (m ≫ v) (ι A₀ A) ⟶ pullback v (ι A₀ A) :=
    pullback.lift (pullback.fst _ _ ≫ m) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hmA1 : mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m := pullback.lift_fst _ _ _
  have hmA2 : mA ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion mA := hA mA hmA1 hmA2
  have : IsAffine (pullback (m ≫ v) (ι A₀ A)) := isAffine_of_isAffineHom mA
  obtain ⟨T₀, hT₀fg, hsT₀, hT₀aff⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback (m ≫ v) s
  have := hT₀aff
  have hsurjA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) (phi (R := ↥T₀) m
    v)) := by
    obtain ⟨-, -, hiff⟩ := stage (R := ↥T₀) m v A mA hmA1 hmA2
    exact hiff.mp (IsClosedImmersion.isAffine_surjective_of_isAffine mA).2
  obtain ⟨T', hT'fg, -, hsurjT'⟩ :=
    Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map (R := ↥T₀) (A := A)
      (phi (R := ↥T₀) m v) (phi_finiteType (R := ↥T₀) m v) hsurjA ∅
  have key : ∀ mT : pullback (m ≫ v) (ι A₀ ↥T') ⟶ pullback v (ι A₀ ↥T'),
      mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mT := by
    intro mT h1 h2
    obtain ⟨hW, hV, hiff⟩ := stage (R := ↥T₀) m v (↥T') mT h1 h2
    have := hW
    have := hV
    exact IsClosedImmersion.of_surjective_of_isAffine mT (hiff.mpr hsurjT')
  obtain ⟨s₀, rfl⟩ := hT₀fg
  obtain ⟨t, rfl⟩ := hT'fg
  refine ⟨(Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s₀ : Set A))) (↑t : Set A)).restrictScalars A₀,
    ?_, ?_, ?_⟩
  · exact ⟨s₀ ∪ t, by rw [Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin]⟩
  · intro x hx
    exact (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s₀ : Set A))) (↑t : Set A)).algebraMap_mem
      (⟨x, hsT₀ hx⟩ : ↥(Algebra.adjoin A₀ (↑s₀ : Set A)))
  · exact key
end IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
