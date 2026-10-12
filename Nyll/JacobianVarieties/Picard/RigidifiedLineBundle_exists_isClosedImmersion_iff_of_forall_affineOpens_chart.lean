/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_exists_isClosedImmersion_iff_of_forall_affineOpens_chart.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.PolarisationRosati
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.RigidifiedLineBundle_nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemePropertyBundle_bijective_algebraMap_sections_pullback

/-!
Closed immersion charts for the triviality locus of a rigidified line bundle glue globally.
Their kernels agree on affine overlaps and define the required closed subscheme.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AffineClosedImmersionDescent
attribute [-instance]
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp]
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans
  AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst
  AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd
  AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl
  AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt
  AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
attribute [-simp]
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Polarisation

noncomputable section

namespace GlueClosed2

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f}
  {X : Scheme.{0}} {g : X ⟶ Spec (CommRingCat.of R)}

/-- The pulled-back line bundle is isomorphic to the unit bundle. -/
def Triv (M : RigidifiedLineBundle f ε g) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t g) : Prop :=
  Nonempty ((M.pullbackAlong ψ).L ≅ (RigidifiedLineBundle.unit (c := f) (ε := ε) t).L)

/-- The composition comparison for pullbacks of a rigidified line bundle. -/
def pullbackAlongComp (M : RigidifiedLineBundle f ε g) {T T' : Scheme.{0}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t g) (φ : SchemeHomOver t' t) :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd f φ) (baseChangeSnd f ψ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp f ψ φ)).app M.L

/-- Pulling back the unit line bundle gives the unit line bundle. -/
def unitPullbackAlong {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {t' : T' ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver t' t) :
    ((RigidifiedLineBundle.unit (c := f) (ε := ε) t).pullbackAlong φ).L ≅
      (RigidifiedLineBundle.unit (c := f) (ε := ε) t').L :=
  Scheme.Modules.pullbackUnitIso (baseChangeSnd f φ)

/-- Triviality is preserved by further pullback. -/
theorem Triv.comp {M : RigidifiedLineBundle f ε g} {T T' : Scheme.{0}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {ψ : SchemeHomOver t g} (h : Triv M t ψ) (φ : SchemeHomOver
      t' t) :
    Triv M t' (postComp ψ φ) := by
  obtain ⟨e⟩ := h
  exact ⟨(pullbackAlongComp M ψ φ).symm ≪≫ (Scheme.Modules.pullback (baseChangeSnd f φ)).mapIso e ≪≫
    unitPullbackAlong t φ⟩

/-- View a morphism to the parameter scheme as a point over its composite base map. -/
abbrev pt {T : Scheme.{0}} (h : T ⟶ X) : SchemeHomOver (h ≫ g) g := ⟨h, rfl⟩

/-- Restrict a point to an open subscheme of its source. -/
abbrev SchemeHomOver.res {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t g)
    (W : T.Opens) :
    SchemeHomOver (W.ι ≫ t) g :=
  postComp ψ ⟨W.ι, rfl⟩

/-- An existing closed chart representing the triviality locus on an open subset. -/
structure Chart (M : RigidifiedLineBundle f ε g) (U : X.Opens) where
  /-- The scheme representing the chart. -/
  Z : Scheme.{0}
  /-- The chart map into the open subscheme. -/
  ι : Z ⟶ (U : Scheme.{0})
  /-- The chart map is a closed immersion. -/
  closed : IsClosedImmersion ι
  /-- Factorization through the chart is equivalent to triviality. -/
  iff : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ (U : Scheme.{0}))
    (hψ : (ψU ≫ U.ι) ≫ g = t),
    Triv M t (⟨ψU ≫ U.ι, hψ⟩ : SchemeHomOver t g) ↔ ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψU

attribute [scoped instance] Chart.closed

namespace Chart

variable {M : RigidifiedLineBundle f ε g} {U : X.Opens} (C : Chart M U)

/-- The composite embedding of a chart into the parameter scheme. -/
abbrev emb : C.Z ⟶ X := C.ι ≫ U.ι

/-- The chart embedding has image in its defining open subset. -/
theorem range_emb : Set.range C.emb.base ⊆ (U : Set X) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← Scheme.Opens.range_ι U]
  exact Set.image_subset_range _ _

/-- The chart represents triviality for any point with image in its open subset. -/
theorem iff' {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t g)
    (hr : Set.range ψ.1.base ⊆ (U : Set X)) :
    Triv M t ψ ↔ ∃ ψ₀ : T ⟶ C.Z, ψ₀ ≫ C.emb = ψ.1 := by
  have hr' : Set.range ψ.1.base ⊆ Set.range U.ι.base := by rwa [Scheme.Opens.range_ι]
  have fac := IsOpenImmersion.lift_fac U.ι ψ.1 hr'
  have key := C.iff t (IsOpenImmersion.lift U.ι ψ.1 hr') (by rw [fac]; exact ψ.2)
  have e : (⟨IsOpenImmersion.lift U.ι ψ.1 hr' ≫ U.ι,
    by rw [fac]; exact ψ.2⟩ : SchemeHomOver t g) = ψ :=
    Subtype.ext fac
  rw [e] at key
  rw [key]
  constructor
  · rintro ⟨ψ₀, h⟩
    exact ⟨ψ₀, by rw [emb, ← Category.assoc, h, fac]⟩
  · rintro ⟨ψ₀, h⟩
    refine ⟨ψ₀, ?_⟩
    rw [← cancel_mono U.ι, Category.assoc, fac]
    exact h

/-- The line bundle is trivial on its representing chart. -/
theorem triv_emb : Triv M (C.emb ≫ g) (pt C.emb) :=
  (C.iff' (pt C.emb) C.range_emb).2 ⟨𝟙 _, Category.id_comp _⟩

end Chart

/-- Restriction to the preimage open does not change the kernel on sections. -/
theorem ker_app_res {T : Scheme.{0}} (h : T ⟶ X) (V : X.Opens) :
    RingHom.ker (((h ⁻¹ᵁ V).ι ≫ h).app V).hom = RingHom.ker (h.app V).hom := by
  have : IsIso ((h ⁻¹ᵁ V).ι.app (h ⁻¹ᵁ V)) :=
    Scheme.Hom.isIso_app _ _ (by rw [Scheme.Opens.opensRange_ι])
  ext x
  simp only [RingHom.mem_ker, Scheme.Hom.comp_app]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso ((h ⁻¹ᵁ V).ι.app (h ⁻¹ᵁ V))).1

/-- Restricting a map to a preimage open gives image in that open. -/
theorem range_res_subset {T : Scheme.{0}} (h : T ⟶ X) (V : X.Opens) :
    Set.range ((h ⁻¹ᵁ V).ι ≫ h).base ⊆ (V : Set X) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  exact Set.image_preimage_subset _ _

/-- The restriction isomorphism from sections on an open to its top sections. -/
abbrev θ (V : X.Opens) : Γ(X, V) ⟶ Γ((V : Scheme.{0}), ⊤) := V.ι.appLE V ⊤ V.ι_preimage_self.ge

scoped instance (V : X.Opens) : IsIso (θ V) := inferInstanceAs (IsIso (V.ι.appLE V ⊤
  V.ι_preimage_self.ge))

/-- Restriction on top sections agrees with the usual top-section map. -/
theorem appLE_top_top_eq_appTop {S T : Scheme.{0}} (k : T ⟶ S) : k.appLE ⊤ ⊤ le_top = k.appTop :=
  (Scheme.Hom.app_eq_appLE k).symm

/-- Compare the kernel after an open inclusion with the kernel on top sections. -/
theorem ker_comp_ι_app {T : Scheme.{0}} (V : X.Opens) (k : T ⟶ (V : Scheme.{0})) :
    RingHom.ker ((k ≫ V.ι).app V).hom = (RingHom.ker k.appTop.hom).comap (θ V).hom := by
  have e : (⊤ : T.Opens) ≤ (k ≫ V.ι) ⁻¹ᵁ V :=
    (show (k ≫ V.ι) ⁻¹ᵁ V = ⊤ by
      rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]).ge
  have h1 : (k ≫ V.ι).app V ≫ T.presheaf.map (homOfLE e).op = θ V ≫ k.appTop := by
    have hk : k.appLE ⊤ ⊤ (Scheme.Hom.preimage_top k).ge = k.appTop :=
      (Scheme.Hom.app_eq_appLE k).symm
    calc
      (k ≫ V.ι).app V ≫ T.presheaf.map (homOfLE e).op =
          (k ≫ V.ι).appLE V ⊤ e := rfl
      _ = θ V ≫ k.appLE ⊤ ⊤ (Scheme.Hom.preimage_top k).ge :=
        (Scheme.Hom.appLE_comp_appLE k V.ι V ⊤ ⊤ V.ι_preimage_self.ge
          (Scheme.Hom.preimage_top k).ge).symm
      _ = θ V ≫ k.appTop := congrArg (fun φ => θ V ≫ φ) hk
  have htop : (k ≫ V.ι) ⁻¹ᵁ V = ⊤ := top_le_iff.mp e
  have hhom : (homOfLE e).op = (eqToHom htop.symm).op := by congr 1
  have : IsIso (T.presheaf.map (homOfLE e).op) := by rw [hhom, eqToHom_op]; infer_instance
  ext x
  rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, ← RingHom.comp_apply, ←
    CommRingCat.hom_comp, ← h1,
    CommRingCat.hom_comp, RingHom.comp_apply]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (T.presheaf.map (homOfLE
    e).op)).1).symm

section Agree

variable {M : RigidifiedLineBundle f ε g} (Z : ∀ U : X.affineOpens, Chart M (U : X.Opens))

/-- The ideal of an affine chart inside the sections of the ambient open. -/
abbrev κ (V : X.affineOpens) : Ideal Γ(X, (V : X.Opens)) := RingHom.ker ((Z V).emb.app V).hom

/-- The ideals of two nested affine charts agree after restriction. -/
theorem ker_emb_app_eq {U V : X.affineOpens} (hVU : (V : X.Opens) ≤ U) :
    RingHom.ker ((Z U).emb.app V).hom = κ Z V := by
  apply le_antisymm
  · obtain ⟨a, ha⟩ := ((Z U).iff' (pt (Z V).emb) (fun x hx => hVU ((Z V).range_emb hx))).1 (Z
      V).triv_emb
    have ha' : a ≫ (Z U).emb = (Z V).emb := ha
    intro x hx
    rw [RingHom.mem_ker] at hx
    change (((Z V).emb).app V).hom x = 0
    rw [← ha', Scheme.Hom.comp_app]
    first
      | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx, map_zero])
      | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx, map_zero])
  · intro x hx
    let h : ((Z U).emb ⁻¹ᵁ (V : X.Opens) : Scheme.{0}) ⟶ X := ((Z U).emb ⁻¹ᵁ (V : X.Opens)).ι ≫ (Z
      U).emb
    have hrV : Set.range h.base ⊆ ((V : X.Opens) : Set X) := range_res_subset (Z U).emb V
    have hT : Triv M _ (pt h) :=
      ((Z U).iff' (pt h) (fun y hy => hVU (hrV hy))).2 ⟨((Z U).emb ⁻¹ᵁ (V : X.Opens)).ι, rfl⟩
    obtain ⟨b, hb⟩ := ((Z V).iff' (pt h) hrV).1 hT
    have hb' : b ≫ (Z V).emb = h := hb
    have hx0 : (((Z V).emb).app V).hom x = 0 := hx
    rw [← ker_app_res (Z U).emb V]
    change x ∈ RingHom.ker (h.app V).hom
    rw [RingHom.mem_ker, ← hb', Scheme.Hom.comp_app]
    first
      | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx0, map_zero])
      | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx0, map_zero])

/-- The chart kernel localizes to the kernel on a basic open. -/
theorem ker_emb_app_map_basicOpen (W : X.affineOpens) (s : Γ(X, (W : X.Opens))) :
    (RingHom.ker ((Z W).emb.app W).hom).map (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
      RingHom.ker ((Z W).emb.app (X.affineBasicOpen s)).hom := by
  change (RingHom.ker ((Z W).emb.app W).hom).map
      (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom =
    RingHom.ker ((Z W).emb.app (X.basicOpen s)).hom
  set h := (Z W).emb with hh
  have hcompact : IsCompact (h ⁻¹ᵁ (W : X.Opens)).1 := by
    have h1 : h ⁻¹ᵁ (W : X.Opens) = (Z W).ι ⁻¹ᵁ ((W : X.Opens).ι ⁻¹ᵁ (W : X.Opens)) := rfl
    rw [h1, Scheme.Opens.ι_preimage_self]
    exact QuasiCompact.isCompact_preimage _ isOpen_univ isCompact_univ
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap]
    change (h.app (X.basicOpen s)).hom ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom x) = 0
    rw [← CommRingCat.comp_apply, h.naturality, CommRingCat.comp_apply, hx, map_zero]
  · intro x hx
    have := W.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices ∃ (V : (Z W).Z.Opens) (hV : V = (Z W).Z.basicOpen ((h.app W).hom s)),
        let _ : V ≤ h ⁻¹ᵁ (W : X.Opens) := hV.trans_le ((Z W).Z.basicOpen_le _); ((h.app W).hom x
          |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        (Z W).Z (U := h ⁻¹ᵁ (W : X.Opens)) hcompact ((h.app W).hom x) ((h.app W).hom s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa only [RingHom.mem_ker, map_mul, map_pow] using hn⟩
    refine ⟨h ⁻¹ᵁ X.basicOpen s, Scheme.preimage_basicOpen h s, ?_⟩
    replace hx : (X.presheaf.map (homOfLE (X.basicOpen_le s)).op ≫ h.app _).hom x = 0 := by
      trans (h.app (X.basicOpen s)).hom (algebraMap Γ(X, (W : X.Opens)) _ x)
      · simp only [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
      · have hx' : (h.app (X.basicOpen s)).hom
            (IsLocalization.mk' (Γ(X, X.basicOpen s)) x (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)) = 0
              := hx
        rw [← IsLocalization.mk'_spec' (Γ(X, X.basicOpen s)) x (⟨s ^ n, n, rfl⟩ : Submonoid.powers
          s), map_mul, hx',
          mul_zero]
    rwa [h.naturality] at hx

/-- The ideal sheaf obtained from the compatible affine chart kernels. -/
def glued : X.IdealSheafData where
  ideal V := κ Z V
  map_ideal_basicOpen V s := by
    rw [ker_emb_app_map_basicOpen Z V s]
    exact ker_emb_app_eq Z (X.basicOpen_le s)

end Agree

/-- The restricted point has image in the specified open subset. -/
theorem range_val_res_subset {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t g) (V : X.Opens) :
    Set.range (SchemeHomOver.res ψ (ψ.1 ⁻¹ᵁ V)).1.base ⊆ (V : Set X) :=
  range_res_subset ψ.1 V

/-- Glue closed charts representing triviality to a global closed subscheme. -/
theorem main
    (hH0 : ∀ (B : Type) [CommRing B] [Algebra R B],
      let _ : Algebra B Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R B), ⊤) :=
        Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd f (Scheme.TwoAffineOpenCover.specMap R B)) ⊤
      Function.Bijective (algebraMap B Γ(Limits.pullback f (Scheme.TwoAffineOpenCover.specMap R B),
        ⊤)))
    (M : RigidifiedLineBundle f ε g) (Z : ∀ U : X.affineOpens, Chart M (U : X.Opens)) :
    ∃ (Zs : Scheme.{0}) (ι : Zs ⟶ X), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Triv M t ψ ↔ ∃ ψ₀ : T ⟶ Zs, ψ₀ ≫ ι = ψ.1 := by
  let I := glued Z
  refine ⟨I.subscheme, I.subschemeι, inferInstance, ?_⟩
  intro T t ψ
  constructor
  · intro hT
    have hle : I ≤ ψ.1.ker := by
      change I ≤ Scheme.IdealSheafData.ofIdeals _
      rw [Scheme.IdealSheafData.le_ofIdeals_iff]
      intro V x hx
      have hT' : Triv M _ (SchemeHomOver.res ψ (ψ.1 ⁻¹ᵁ (V : X.Opens))) := hT.comp _
      obtain ⟨ψ₀, h₀⟩ := ((Z V).iff' _ (range_val_res_subset ψ V)).1 hT'
      have h₀' : ψ₀ ≫ (Z V).emb = (ψ.1 ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ.1 := h₀
      have hx0 : (((Z V).emb).app V).hom x = 0 := hx
      change x ∈ RingHom.ker (ψ.1.app V).hom
      rw [← ker_app_res ψ.1 V, RingHom.mem_ker]
      rw [← h₀', Scheme.Hom.comp_app]
      first
        | (simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hx0, map_zero])
        | (erw [CommRingCat.hom_comp]; rw [RingHom.comp_apply, hx0, map_zero])
    exact ⟨IsClosedImmersion.lift I.subschemeι ψ.1
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hle),
      IsClosedImmersion.lift_fac _ _ _⟩
  · rintro ⟨ψ₀, hψ₀⟩
    have hIψ : ∀ V : X.affineOpens, κ Z V ≤ RingHom.ker (ψ.1.app V).hom := fun V => by
      have h1 : I ≤ ψ.1.ker := by
        rw [← hψ₀]
        have := Scheme.Hom.le_ker_comp ψ₀ I.subschemeι
        rwa [Scheme.IdealSheafData.ker_subschemeι] at this
      exact (Scheme.IdealSheafData.ideal_mono h1 V).trans (ψ.1.ideal_ker_le V)
    have key : ∀ V : X.affineOpens, Triv M _ (SchemeHomOver.res ψ (ψ.1 ⁻¹ᵁ (V : X.Opens))) := by
      intro V
      let hV : (ψ.1 ⁻¹ᵁ (V : X.Opens) : Scheme.{0}) ⟶ X := (ψ.1 ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ.1
      have hr : Set.range hV.base ⊆ ((V : X.Opens) : Set X) := range_res_subset ψ.1 V
      have hr' : Set.range hV.base ⊆ Set.range (V : X.Opens).ι.base := by rwa [Scheme.Opens.range_ι]
      let k := IsOpenImmersion.lift (V : X.Opens).ι hV hr'
      have hk : k ≫ (V : X.Opens).ι = hV := IsOpenImmersion.lift_fac _ _ _
      have hkerTop : RingHom.ker ((Z V).ι.appTop).hom ≤ RingHom.ker (k.appTop).hom := by
        intro x' hx'
        obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (θ (V : X.Opens))).2 x'
        have m1 : x ∈ RingHom.ker (((Z V).ι ≫ (V : X.Opens).ι).app V).hom := by
          rw [ker_comp_ι_app]; exact hx'
        have m2 : x ∈ RingHom.ker (hV.app V).hom := by
          change x ∈ RingHom.ker ((((ψ.1 ⁻¹ᵁ (V : X.Opens)).ι ≫ ψ.1)).app V).hom
          rw [ker_app_res]
          exact hIψ V m1
        rw [← hk, ker_comp_ι_app] at m2
        exact m2
      have hle : (Z V).ι.ker ≤ k.ker := by
        rw [Scheme.ker_of_isAffine k]
        refine Scheme.IdealSheafData.le_of_isAffine ?_
        rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ofIdealTop_ideal]
        intro y hy
        have hid : (homOfLE (le_top : (⊤ : ((V : X.Opens) : Scheme.{0}).Opens) ≤ ⊤)) = 𝟙 _ :=
          Subsingleton.elim _ _
        have hy' : y = (((V : X.Opens) : Scheme.{0}).presheaf.map (homOfLE le_top).op).hom y := by
          rw [hid, op_id, CategoryTheory.Functor.map_id]; rfl
        rw [hy']
        exact Ideal.mem_map_of_mem _ (hkerTop hy)
      refine ((Z V).iff' _ hr).2 ⟨IsClosedImmersion.lift (Z V).ι k hle, ?_⟩
      change (IsClosedImmersion.lift (Z V).ι k hle ≫ ((Z V).ι ≫ (V : X.Opens).ι)) = hV
      rw [← Category.assoc, IsClosedImmersion.lift_fac, hk]
    have hf : ∀ x : T, ∃ V : X.affineOpens,
        x ∈ Set.range (⟨(ψ.1 ⁻¹ᵁ (V : X.Opens)).ι, rfl⟩ : SchemeHomOver ((ψ.1 ⁻¹ᵁ (V : X.Opens)).ι
          ≫ t) t).1.base := by
      intro x
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ψ.1.base x)) isOpen_univ
      exact ⟨⟨V, hV⟩, by rw [Scheme.Opens.range_ι]; exact hxV⟩
    obtain ⟨e⟩ :=
      RigidifiedLineBundle.nonempty_iso_of_pullbackAlong_openCover_of_bijective_sections R f ε hH0 t
      (fun V : X.affineOpens => (ψ.1 ⁻¹ᵁ (V : X.Opens)).ι ≫ t)
      (fun V : X.affineOpens => (⟨(ψ.1 ⁻¹ᵁ (V : X.Opens)).ι, rfl⟩ : SchemeHomOver ((ψ.1 ⁻¹ᵁ (V :
        X.Opens)).ι ≫ t) t))
      hf (M.pullbackAlong ψ) (RigidifiedLineBundle.unit t) (fun V => by
        obtain ⟨e⟩ := key V
        exact ⟨pullbackAlongComp M ψ _ ≪≫ e ≪≫ (unitPullbackAlong t _).symm⟩)
    exact ⟨e⟩

end GlueClosed2

open scoped
  _root_.JacobianVarieties.Picard.Proofs.AffineClosedImmersionDescent.GlueClosed2

end

open scoped
  _root_.JacobianVarieties.Picard.Proofs.AffineClosedImmersionDescent.GlueClosed2

end JacobianVarieties.Picard.Proofs.AffineClosedImmersionDescent

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open _root_.JacobianVarieties.Picard.Proofs.AffineClosedImmersionDescent in
/-- Local closed immersion charts for triviality glue to a global representing closed immersion. -/
theorem
exists_isClosedImmersion_iff_of_forall_affineOpens_chart
    {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (hA : AbelianSchemePropertyBundle R f)
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle f (L.one (𝟙 (Spec (CommRingCat.of R)))) g)
    (hloc : ∀ U : X.affineOpens, ∃ (ZU : Scheme.{0}) (ιU : ZU ⟶ ((U : X.Opens) : Scheme.{0})),
      IsClosedImmersion ιU ∧
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψU : T ⟶ ((U : X.Opens) : Scheme.{0}))
          (hψ : (ψU ≫ (U : X.Opens).ι) ≫ g = t),
          (Nonempty ((M.pullbackAlong (⟨ψU ≫ (U : X.Opens).ι, hψ⟩ : SchemeHomOver t g)).L ≅
              (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
            ∃ ψ₀ : T ⟶ ZU, ψ₀ ≫ ιU = ψU)) :
    ∃ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t g),
        Nonempty ((M.pullbackAlong ψ).L ≅
            (RigidifiedLineBundle.unit (c := f) (ε := L.one (𝟙 (Spec (CommRingCat.of R)))) t).L) ↔
          ∃ ψ₀ : T ⟶ Z, ψ₀ ≫ ι = ψ.1 := by
  let Z : ∀ U : X.affineOpens, GlueClosed2.Chart M (U : X.Opens) := fun U =>
    ⟨(hloc U).choose, (hloc U).choose_spec.choose, (hloc U).choose_spec.choose_spec.1,
      fun t ψU hψ => (hloc U).choose_spec.choose_spec.2 t ψU hψ⟩
  exact GlueClosed2.main hA.bijective_algebraMap_sections_pullback M Z
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

attribute [-instance]
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
  TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower
  TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free
  AlgebraicGeometry.SubalgebraStages.compactSpace_pullback
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback
  AlgebraicGeometry.SubalgebraStages.compactSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj
  AlgebraicGeometry.SubalgebraStages.quasiCompact_snd
  AlgebraicGeometry.SubalgebraStages.isAffineHom_leg
  AlgebraicGeometry.SubalgebraStages.isAffineHom_trans
  AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map
  AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd
  AlgebraicGeometry.SubalgebraStages.isCofiltered_op
  IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty
  AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp]
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0
  TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq
  TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec
  TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply
  TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply
  CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq
  AlgebraicGeometry.SubalgebraStages.specCone_π_app
  AlgebraicGeometry.SubalgebraStages.specLeg_specHom
  AlgebraicGeometry.SubalgebraStages.specLeg_specTrans
  AlgebraicGeometry.SubalgebraStages.cone_pt
  AlgebraicGeometry.SubalgebraStages.trans_fst
  AlgebraicGeometry.SubalgebraStages.diagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_snd
  AlgebraicGeometry.SubalgebraStages.diagram_map
  AlgebraicGeometry.SubalgebraStages.specTrans_refl
  AlgebraicGeometry.SubalgebraStages.trans_snd
  AlgebraicGeometry.SubalgebraStages.specTrans_specHom
  AlgebraicGeometry.SubalgebraStages.specCone_pt
  AlgebraicGeometry.SubalgebraStages.cone_π_app
  AlgebraicGeometry.SubalgebraStages.specDiagram_map
  AlgebraicGeometry.SubalgebraStages.specDiagram_obj
  AlgebraicGeometry.SubalgebraStages.leg_fst
  AlgebraicGeometry.SubalgebraStages.leg_trans
  IsDirectLimit.Module.linearEquiv_symm_apply
  IsDirectLimit.linearEquiv_symm_apply
  IsDirectLimit.lift_of
  IsDirectLimit.Module.linearEquiv_apply
  IsDirectLimit.Module.lift_of
  IsDirectLimit.Equiv_apply
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe
attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe
  GoodReductionJacobian.RelativeGroupLaw.baseChange_inv
  GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.baseChange_mul
  GoodReductionJacobian.RelativeGroupLaw.baseChange_one
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst
  NeronModelInfra.fibreRestrictAlong_coe_comp_fst_assoc
  NeronModelInfra.fibreRestrictAlong_coe_comp_snd_assoc
  GoodReductionJacobian.RelativeGroupLaw.fibre_inv
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_mul
  GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase
  GoodReductionJacobian.RelativeGroupLaw.fibre_one
  GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe
  AlgebraicGeometry.schemeFibreEndo_snd
  AlgebraicGeometry.schemeFibreEndo_fst
