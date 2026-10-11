/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Choose
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.SchemeTheory.Modules.TensorSections
import Nyll.SchemeTheory.Modules.FrameFromTrivialization
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_of_iSup

/-!
# Scheme Modules nonempty iso unit of forall pullback rig Section iso unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard

namespace S1C
namespace NodeTriv

/-- The canonical comparison from an iterated pullback to pullback along the composite. -/
noncomputable def pb2 {X₀ X₁ X₂ : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (L : X₂.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback
      (f ≫ g)).obj L :=
  (Scheme.Modules.pullbackComp f g).app L

theorem nonempty_iso_unit_of_iso_comp {X Y Y' : Scheme.{u}} {K : X.Modules} (f : Y ⟶ X) (f' : Y' ⟶
  X) (e : Y' ⟶ Y)
    [IsIso e] (hef : e ≫ f = f')
    (h : Nonempty ((Scheme.Modules.pullback f).obj K ≅ SheafOfModules.unit Y.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj K ≅ SheafOfModules.unit Y'.ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackCongr hef.symm).app K ≪≫ (pb2 e f K).symm ≪≫
    (Scheme.Modules.pullback e).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso e⟩

theorem nonempty_iso_unit_of_iSup_eq_top_of_pairwise_disjoint
    {Y : Scheme.{u}} (N : Y.Modules) {ι' : Type*} (V : ι' → Y.Opens) (hV : ⨆ i, V i = ⊤)
    (hdisj : Pairwise fun i j => Disjoint (V i) (V j))
    (htriv : ∀ i, Nonempty ((Scheme.Modules.pullback (V i).ι).obj N ≅ SheafOfModules.unit (V
      i).toScheme.ringCatSheaf)) :
    Nonempty (N ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  classical
  choose s hs using fun i => Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (M := N) (V i)
    (htriv i).some
  let F : TopCat.Sheaf Ab Y.toPresheafedSpace := ⟨N.presheaf, N.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.obj V s := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · have hbot : V i ⊓ V j = ⊥ := (hdisj hij).eq_bot
      apply F.eq_of_locally_eq' (fun e : PEmpty.{1} => e.elim) (V i ⊓ V j) (fun e => e.elim)
      · rw [hbot]; exact bot_le
      · intro e; exact e.elim
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) (by rw [hV]) s hcompat
  have hframe : ∀ i, Scheme.Modules.IsFrameOn (t : Γ(N, ⊤)) (V i) := by
    intro i W hWU hWV
    have key : N.presheaf.map (homOfLE hWU).op t = N.presheaf.map (homOfLE hWV).op (s i) := by
      rw [← ht i, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    have hb := hs i hWV hWV
    simp only [← key] at hb
    exact hb
  have htop : Scheme.Modules.IsFrameOn (t : Γ(N, ⊤)) (⊤ : Y.Opens) := by
    have h := Scheme.Modules.IsFrameOn.of_iSup V hframe
    rwa [hV] at h
  obtain ⟨e⟩ := htop.nonempty_pullback_iso_unit ⊤ le_rfl le_rfl
  have : IsIso (⊤ : Y.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  refine ⟨((Scheme.Modules.pullbackId Y).app N).symm ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id (⊤ : Y.Opens).ι).symm).app N ≪≫
    (pb2 (inv (⊤ : Y.Opens).ι) (⊤ : Y.Opens).ι N).symm ≪≫
    (Scheme.Modules.pullback (inv (⊤ : Y.Opens).ι)).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem isOpenImmersion_of_rationalPoint
    {k : Type u} [Field k] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k))
    [IsSeparated z] [IsReduced Z] [DiscreteTopology Z]
    (ζ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) z) : IsOpenImmersion ζ.1 := by
  have : IsClosedImmersion (ζ.1 ≫ z) := by rw [ζ.2]; infer_instance
  have : IsClosedImmersion ζ.1 := IsClosedImmersion.of_comp ζ.1 z
  let W : Z.Opens := ⟨{ζ.1.base (IsLocalRing.closedPoint k)}, isOpen_discrete _⟩
  have hfw : ∀ p : Spec (CommRingCat.of k), ζ.1.base p = ζ.1.base (IsLocalRing.closedPoint k) :=
    fun p => by
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
  have hpre : ζ.1 ⁻¹ᵁ W = ⊤ := by
    ext p
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, TopologicalSpace.Opens.coe_top,
      Set.mem_univ,
      iff_true]
    exact hfw p
  have : IsClosedImmersion (ζ.1 ∣_ W) := IsZariskiLocalAtTarget.restrict ‹_› W
  have : Surjective (ζ.1 ∣_ W) := by
    let p : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
    have hp : p ∈ ζ.1 ⁻¹ᵁ W := by rw [hpre]; trivial
    let q : ζ.1 ⁻¹ᵁ W := ⟨p, hp⟩
    refine ⟨fun y => ⟨q, ?_⟩⟩
    apply Subtype.ext
    have hy : y.1 = ζ.1.base p := y.2
    exact (morphismRestrict_base_coe ζ.1 W q).trans hy.symm
  have : IsIso (ζ.1 ∣_ W) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (ζ.1 ⁻¹ᵁ W).ι := by rw [hpre, ← Scheme.topIso_hom]; infer_instance
  have hfac : ζ.1 = inv (ζ.1 ⁻¹ᵁ W).ι ≫ (ζ.1 ∣_ W) ≫ W.ι := by
    rw [IsIso.eq_inv_comp, morphismRestrict_ι]
  rw [hfac]; infer_instance

end S1C.NodeTriv

open S1C.NodeTriv in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
    {k : Type u} [Field k] {Z T : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k)) [IsSeparated z]
      [IsReduced Z] [Finite Z]
    (t : T ⟶ Spec (CommRingCat.of k)) {ι : Type v} (ζ : ι → SchemeHomOver (𝟙 (Spec (CommRingCat.of
      k))) z)
    (hcov : ∀ w : Z, ∃ j, (ζ j).1.base (IsLocalRing.closedPoint k) = w)
    (F : (Limits.pullback z t).Modules)
    (htriv : ∀ j, Nonempty ((Scheme.Modules.pullback (rigSection z t (ζ j))).obj F ≅
      SheafOfModules.unit T.ringCatSheaf)) :
    Nonempty (F ≅ SheafOfModules.unit (Limits.pullback z t).ringCatSheaf) := by
  classical
  choose jw hjw using hcov
  have hci : ∀ j, IsClosedImmersion (ζ j).1 := fun j => by
    have : IsClosedImmersion ((ζ j).1 ≫ z) := by rw [(ζ j).2]; infer_instance
    exact IsClosedImmersion.of_comp (ζ j).1 z
  have hrange : ∀ j, Set.range (ζ j).1.base = {(ζ j).1.base (IsLocalRing.closedPoint k)} := fun j
    => by
    ext p
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, rfl⟩; rw [Subsingleton.elim q (IsLocalRing.closedPoint k)]
    · intro hp; exact ⟨IsLocalRing.closedPoint k, hp.symm⟩
  have : T1Space Z := ⟨fun w => by
    rw [← hjw w, ← hrange (jw w)]
    have : IsClosedImmersion (ζ (jw w)).1 := hci (jw w)
    exact (ζ (jw w)).1.isClosedEmbedding.isClosed_range⟩
  have : DiscreteTopology Z := inferInstance
  have : ∀ j, IsOpenImmersion (ζ j).1 := fun j => isOpenImmersion_of_rationalPoint z (ζ j)
  let np : ∀ w : Z, pullback (pullback.fst z t) (ζ (jw w)).1 ⟶ pullback z t := fun w =>
    pullback.fst _ _
  let V : ↥Z → (pullback z t).Opens := fun w => Scheme.Hom.opensRange (np w)
  have hVmem : ∀ w p, p ∈ V w ↔ (pullback.fst z t).base p = w := fun w p => by
    change p ∈ Set.range (np w).base ↔ _
    simp only [np]
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hrange, hjw, Set.mem_singleton_iff]
  have hVcov : ⨆ w, V w = ⊤ := by
    rw [eq_top_iff]
    rintro p -
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨(pullback.fst z t).base p, (hVmem _ p).mpr rfl⟩
  have hVdisj : Pairwise fun w w' => Disjoint (V w) (V w') := by
    intro w w' hww'
    rw [disjoint_iff, eq_bot_iff]
    rintro p ⟨hp, hp'⟩
    exact hww' (((hVmem w p).mp hp).symm.trans ((hVmem w' p).mp hp'))
  let n : ∀ w : Z, T ⟶ pullback z t := fun w => rigSection z t (ζ (jw w))
  have hn_fst : ∀ w, n w ≫ pullback.fst z t = t ≫ (ζ (jw w)).1 := fun w => by
    simp only [n, rigSection, pullback.lift_fst]
  have hn_snd : ∀ w, n w ≫ pullback.snd z t = 𝟙 _ := fun w => by
    simp only [n, rigSection, pullback.lift_snd]
  let e : ∀ w : Z, pullback (pullback.fst z t) (ζ (jw w)).1 ⟶ T := fun w => np w ≫ pullback.snd z t
  have he_t : ∀ w, e w ≫ t = pullback.snd (pullback.fst z t) (ζ (jw w)).1 := fun w => by
    simp only [e, np, Category.assoc]
    rw [← pullback.condition, pullback.condition_assoc, (ζ (jw w)).2, Category.comp_id]
  have he_n : ∀ w, e w ≫ n w = np w := fun w => by
    apply pullback.hom_ext
    · rw [Category.assoc, hn_fst, ← Category.assoc, he_t]
      simp only [np]
      exact pullback.condition.symm
    · rw [Category.assoc, hn_snd, Category.comp_id]
  let eInv : ∀ w : Z, T ⟶ pullback (pullback.fst z t) (ζ (jw w)).1 := fun w => pullback.lift (n w)
    t (hn_fst w)
  have hInv_np : ∀ w, eInv w ≫ np w = n w := fun w => by simp only [eInv, np, pullback.lift_fst]
  have h1 : ∀ w, eInv w ≫ e w = 𝟙 _ := fun w => by
    simp only [e]
    rw [← Category.assoc, hInv_np, hn_snd]
  have h2 : ∀ w, e w ≫ eInv w = 𝟙 _ := fun w => by
    apply pullback.hom_ext
    · rw [Category.assoc, hInv_np, he_n, Category.id_comp]
    · rw [Category.assoc, Category.id_comp]
      simp only [eInv, pullback.lift_snd]
      exact he_t w
  have : ∀ w, IsIso (e w) := fun w => ⟨⟨eInv w, h2 w, h1 w⟩⟩
  refine nonempty_iso_unit_of_iSup_eq_top_of_pairwise_disjoint F V hVcov hVdisj fun w => ?_
  have hpiece := nonempty_iso_unit_of_iso_comp (K := F) (n w) (np w) (e w) (he_n w) (htriv (jw w))
  exact nonempty_iso_unit_of_iso_comp (np w) (V w).ι (Scheme.Hom.isoOpensRange (np w)).inv
    (Scheme.Hom.isoOpensRange_inv_comp (np w)) hpiece
end Scheme_Modules_nonempty_iso_unit_of_forall_pullback_rigSection_iso_unit
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation

open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  PresheafOfModules.instMonoidalClosed
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
