/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_isFinite_of_isIso_stalkMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Cech.DivisorSections
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.IsClosed_singleton_of_ne_genericPoint
import AlgebraicCurves.Models.CurveModel_apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
import AlgebraicCurves.Models.CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap

/-!
# Curve Model is Finite of is Iso stalk Map
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_isFinite_of_isIso_stalkMap
open _root_.AlgebraicCurve.CurveModel

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

namespace NuFinK11

theorem eq_genericPoint_of_isField {C : Scheme.{u}} [IsIntegral C] (x : C)
    (hfield : IsField (C.presheaf.stalk x)) : x = genericPoint C := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let := C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨_, hxU⟩
  have hbot : (hU.primeIdealOf ⟨_, hxU⟩).asIdeal = ⊥ := by
    rw [← Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (C.presheaf.stalk x)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hxU⟩).asIdeal,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  have h1 : hU.primeIdealOf ⟨_, hxU⟩ = hU.primeIdealOf ⟨genericPoint C,
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
        (by simpa using (inferInstance : Nonempty U))⟩ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congr(hU.fromSpec $h1)
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2

theorem stalkSpecializes_surjective_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x x' : X) (h
  : x ⤳ x')
    (he : f.base x = f.base x') [IsIso (f.stalkMap x)] :
    Function.Surjective (X.presheaf.stalkSpecializes h) := by
  have hY : ∀ {a b : Y} (eab : a = b) (hab : a ⤳ b), Function.Bijective
    (Y.presheaf.stalkSpecializes hab) := by
    intro a b eab hab
    subst eab
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact Function.bijective_id
  intro t
  obtain ⟨s, hs⟩ := (hY he (f.base.hom.map_specializes h)).2 (inv (f.stalkMap x) t)
  refine ⟨f.stalkMap x' s, ?_⟩
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, hs]
  change (inv (f.stalkMap x) ≫ f.stalkMap x) t = t
  rw [IsIso.inv_hom_id]
  rfl

theorem eq_genericPoint_of_stalkSpecializes_surjective {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hsurj : Function.Surjective (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
      (Set.mem_univ x)))) :
    x = genericPoint X := by
  apply eq_genericPoint_of_isField
  have hinj : Function.Injective (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
    (Set.mem_univ x))) :=
    IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  exact (RingEquiv.ofBijective (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes
    (Set.mem_univ x))).hom
    ⟨hinj, hsurj⟩).toMulEquiv.isField (Field.toIsField X.functionField)

theorem finite_of_isClosed_of_forall_isClosed_singleton {α : Type*} [TopologicalSpace α]
  [NoetherianSpace α] [QuasiSober α]
    (Z : Set α) (hZ : IsClosed Z) (hpt : ∀ z ∈ Z, IsClosed ({z} : Set α)) : Z.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, rfl⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  refine hSfin.sUnion fun t ht => (Set.finite_singleton (hSirr t ht).genericPoint).subset fun z hz
    => ?_
  have hgen := (hSirr t ht).isGenericPoint_genericPoint (hSclosed t ht)
  have hmem : (hSirr t ht).genericPoint ∈ t := hgen.mem
  have hcl := (hpt _ (Set.mem_sUnion_of_mem hmem ht)).closure_eq
  have hz' : z ∈ closure ({(hSirr t ht).genericPoint} : Set α) := by
    rw [hgen.def]; exact hz
  rwa [hcl] at hz'

end NuFinK11

theorem _root_.AlgebraicCurve.CurveModel.isFinite_of_isIso_stalkMap
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
      [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    IsFinite ν := by
  have : IsProper ν := by
    have : IsProper (ν ≫ c) := hν ▸ inferInstance
    exact IsProper.of_comp ν c
  have : IsLocallyNoetherian M.C := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : CompactSpace M.C := by
    have h1 : QuasiCompact (Limits.terminal.from (Spec (CommRingCat.of k))) :=
      (compactSpace_iff_quasiCompact _).mp inferInstance
    have h2 : QuasiCompact (M.toBase ≫ Limits.terminal.from _) := inferInstance
    rw [Limits.terminal.comp_from] at h2
    exact (compactSpace_iff_quasiCompact _).mpr h2
  have : IsNoetherian M.C := {}
  have hη : ν.base (genericPoint M.C) = genericPoint C :=
    (apply_genericPoint_eq_and_nonempty_algEquiv_functionField_of_isIso_stalkMap
      k c M ν hν hbir).1
  have hpts :=
    (surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
      k c M ν hν hbir).2
  have hgenfib : ∀ x : M.C, ν.base x = genericPoint C → x = genericPoint M.C := by
    intro x hx
    apply NuFinK11.eq_genericPoint_of_stalkSpecializes_surjective
    have := hbir
    exact NuFinK11.stalkSpecializes_surjective_of_isIso_stalkMap ν (genericPoint M.C) x _
      (hη.trans hx.symm)
  have : LocallyQuasiFinite ν := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    by_cases hz : z = genericPoint C
    · subst hz
      refine (Set.finite_singleton (genericPoint M.C)).subset fun x hx => ?_
      exact hgenfib x hx
    · have hzc : IsClosed ({z} : Set C) := (hpts z).resolve_left hz
      refine NuFinK11.finite_of_isClosed_of_forall_isClosed_singleton _ (hzc.preimage
        ν.base.hom.continuous) ?_
      intro x hx
      refine AlgebraicCurve.isClosed_singleton_of_ne_genericPoint M.toBase x fun hxη => hz ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      rw [← hx, hxη, hη]
  exact IsFinite.of_isProper_of_locallyQuasiFinite ν

end AlgebraicCurves.Models.Proofs.CurveModel_isFinite_of_isIso_stalkMap
end ProofImplementation
