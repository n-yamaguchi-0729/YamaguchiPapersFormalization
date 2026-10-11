/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.GenericComplementCoverExtension
import Nyll.EtaleFundamentalGroups.FiniteEtale.CompatibleStalkCoverSpreading
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackIdentity
import Nyll.SchemeTheory.FiniteEtale.MaximalOpenExtension
import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# Extending finite étale covers by local purity

On a topologically Noetherian scheme, local purity at all points outside an
open implies that every finite étale cover of the open extends globally.
At a generic missing point, local purity, spreading, and two-open gluing
would enlarge a maximal extension. Consequently its domain is the whole
scheme. This proves Stacks Project, Lemma 58.21.6 (tag `0EY7`).
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

/-- Local purity along the missing points extends all finite étale covers
of the open. Only topological Noetherianity of the ambient scheme is needed
in addition to the stated local purity. -/
theorem pullback_essSurj_of_hasPuncturedPurity
    {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ x : X, x ∉ U → HasPuncturedPurity (X.presheaf.stalk x)) :
    (pullback U.ι).EssSurj := by
  constructor
  intro V
  obtain ⟨N, hUN, W, ⟨eW⟩, hmax⟩ := exists_maximal_open_extension U V
  have hN : N = ⊤ := by
    apply top_unique
    intro z _
    by_contra hzN
    let zC : {z : X // z ∉ N} := ⟨z, hzN⟩
    have hclosed : IsClosed {z : X | z ∉ N} := N.isOpen.isClosed_compl
    have : QuasiSober {z : X // z ∉ N} :=
      hclosed.isClosedEmbedding_subtypeVal.quasiSober
    let Z : irreducibleComponents {z : X // z ∉ N} :=
      ⟨irreducibleComponent zC, irreducibleComponent_mem_irreducibleComponents zC⟩
    let x : genericPoints {z : X // z ∉ N} := genericPoints.ofComponent Z
    have hxU : x.1.1 ∉ U := fun hx => x.1.2 (hUN hx)
    obtain ⟨L, ⟨a⟩⟩ := exists_stalk_cover_extension_of_generic_complement N x
      (hpurity x.1.1 hxU) W
    let : NoetherianSpace N.toScheme :=
      N.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
    obtain ⟨M, hxM, B, ⟨b⟩⟩ := exists_compatible_open_cover_fromSpecStalk
      X N x.1.1 W L a
    obtain ⟨C, hCN, _⟩ := exists_glued_over_sup X N M W B b.symm
    have hNM : N ⊔ M ≤ N := hmax (N ⊔ M) le_sup_left C hCN
    exact x.1.2 (hNM ((show M ≤ N ⊔ M from le_sup_right) hxM))
  let eN : N.toScheme ≅ X := X.isoOfEq hN ≪≫ X.topIso
  have heN : eN.hom = N.ι := X.isoOfEq_hom_ι hN
  have hUi : X.homOfLE hUN = U.ι ≫ eN.inv := by
    apply (cancel_mono eN.hom).mp
    rw [Category.assoc, eN.inv_hom_id, Category.comp_id, heN, Scheme.homOfLE_ι]
  let c : pullback (X.homOfLE hUN) ≅ pullback eN.inv ⋙ pullback U.ι :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      U.ι eN.inv (X.homOfLE hUN) hUi
  exact ⟨(pullback eN.inv).obj W, ⟨(c.app W).symm ≪≫ eW⟩⟩

/-- For an arbitrary open immersion, local purity outside its image extends
every finite etale cover of its source. This is the open-immersion form of
Stacks Project, Lemma 58.21.6 (`0EY7`). -/
theorem pullback_essSurj_of_isOpenImmersion_of_hasPuncturedPurity
    {U X : Scheme.{u}} [NoetherianSpace X]
    (j : U ⟶ X) [IsOpenImmersion j]
    (hpurity : ∀ x : X, x ∉ Set.range j → HasPuncturedPurity (X.presheaf.stalk x)) :
    (pullback j).EssSurj := by
  let O : X.Opens := j.opensRange
  let e : U ≅ O.toScheme := j.isoOpensRange
  have hj : j = e.hom ≫ O.ι := j.isoOpensRange_hom_ι.symm
  have hO : (pullback O.ι).EssSurj :=
    pullback_essSurj_of_hasPuncturedPurity O (fun x hx => hpurity x hx)
  constructor
  intro V
  obtain ⟨Z, ⟨a⟩⟩ := hO.mem_essImage ((pullback e.inv).obj V)
  let c : pullback j ≅ pullback O.ι ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom O.ι j hj
  let d : pullback (𝟙 U) ≅ pullback e.inv ⋙ pullback e.hom :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      e.hom e.inv (𝟙 U) e.hom_inv_id.symm
  exact ⟨Z, ⟨c.app Z ≪≫ (pullback e.hom).mapIso a ≪≫
    (d.app V).symm ≪≫ (pullbackIdIso U).app V⟩⟩

end AlgebraicGeometry.FiniteEtale
