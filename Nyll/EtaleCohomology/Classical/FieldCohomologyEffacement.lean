/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.FreeAbelianYoneda
import Nyll.EtaleCohomology.Sites.FieldFiniteCover
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Finite étale effacement of actual field cohomology classes

Every positive-degree class in the actual Ext-defined cohomology presheaf
over a field vanishes after a connected finite étale cover. The proof uses
the actual injective presentation and the Ext long exact sequence. In degree
one, the connecting class vanishes after locally lifting the corresponding
section; higher degrees follow by dimension shifting and naturality of Ext
composition. No field/Galois comparison or acyclicity assumption is introduced.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.Abelian

namespace EtaleCohomology

/-- Positive-degree actual sheaf cohomology classes over a field vanish
after restriction to a connected finite étale surjective cover. Here
restriction is precisely the map in mathlib's Ext-defined cohomology presheaf. -/
theorem exists_finiteEtale_killing_cohomologyPresheaf_class_of_field
    (K : Type u) [Field K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ)
    (c : Sheaf.H'.{u} F (n + 1) (Scheme.Etale.mk (𝟙 (Spec (.of K))))) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧ Function.Surjective V.hom ∧
        (F.cohomologyPresheaf (n + 1)).map f.op c = 0 := by
  let P : (Spec (.of K)).Etale ⥤
      Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} :=
    freeAbelianSheafYoneda (Spec (.of K)).smallEtaleTopology
  let T : (Spec (.of K)).Etale := Scheme.Etale.mk (𝟙 (Spec (.of K)))
  induction n generalizing F with
  | zero =>
      let S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ (P.obj T) hS c
        (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
      obtain ⟨a, ha⟩ := (Ext.mk₀_bijective (P.obj T) S.X₃).surjective b
      let t : S.X₃.obj.obj (op T) :=
        freeAbelianSheafYonedaHomEquiv _ T S.X₃ a
      have : Epi S.g := hS.epi_g
      obtain ⟨V, f, hf, hc, hs, s, he⟩ :=
        exists_finiteEtale_lift_sheaf_epi_section_of_field K S.g t
      let aV : P.obj V ⟶ S.X₂ :=
        (freeAbelianSheafYonedaHomEquiv _ V S.X₂).symm s
      have heq : aV ≫ S.g = P.map f ≫ a := by
        apply (freeAbelianSheafYonedaHomEquiv _ V S.X₃).injective
        rw [freeAbelianSheafYonedaHomEquiv_postcomp,
          freeAbelianSheafYonedaHomEquiv_precomp]
        change S.g.hom.app (op V)
          (freeAbelianSheafYonedaHomEquiv _ V S.X₂
            ((freeAbelianSheafYonedaHomEquiv _ V S.X₂).symm s)) = _
        rw [Equiv.apply_symm_apply]
        exact he
      refine ⟨V, f, hf, hc, hs, ?_⟩
      change (Ext.mk₀ (P.map f)).comp c (zero_add 1) = 0
      rw [← hb, ← ha, ← Ext.comp_assoc_of_second_deg_zero,
        Ext.mk₀_comp_mk₀, ← heq, ← Ext.mk₀_comp_mk₀,
        Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]
  | succ n ih =>
      let S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ (P.obj T) hS c
        (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
      obtain ⟨V, f, hf, hc, hs, he⟩ := ih S.X₃ b
      refine ⟨V, f, hf, hc, hs, ?_⟩
      change (Ext.mk₀ (P.map f)).comp b (zero_add (n + 1)) = 0 at he
      change (Ext.mk₀ (P.map f)).comp c (zero_add (n + 1 + 1)) = 0
      rw [← hb, ← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl
        (by omega), he, Ext.zero_comp]

private def fieldEtaleTerminal (K : Type u) [Field K] :
    IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
  IsTerminal.ofUniqueHom
    (fun V => MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @AlgebraicGeometry.Etale)
      (Q := ⊤) V.hom (Category.comp_id V.hom))
    (fun V f => MorphismProperty.Over.Hom.ext
      (by
        change f.left = V.hom
        have h : f.left ≫ 𝟙 (Spec (.of K)) = V.hom :=
          MorphismProperty.Over.w f
        exact (Category.comp_id f.left).symm.trans h))

/-- Actual classical sheaf cohomology over a field has finite étale
effacement in every positive degree, via its canonical terminal-object
identification with the actual cohomology presheaf. -/
theorem exists_finiteEtale_killing_sheafCohomology_class_of_field
    (K : Type u) [Field K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ) (c : Sheaf.H.{u} F (n + 1)) :
    ∃ (V : (Spec (.of K)).Etale)
      (f : V ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      IsFinite V.hom ∧ ConnectedSpace V.left ∧ Function.Surjective V.hom ∧
        (F.cohomologyPresheaf (n + 1)).map f.op
          (sheafCohomologyTerminalEquiv _ (fieldEtaleTerminal K) F (n + 1) c) = 0 :=
  exists_finiteEtale_killing_cohomologyPresheaf_class_of_field K F n
    (sheafCohomologyTerminalEquiv _ (fieldEtaleTerminal K) F (n + 1) c)

/-- The effacing cover may be taken from the actual finite Galois
intermediate fields of the algebraic closure in characteristic zero. -/
theorem exists_finiteGalois_killing_cohomologyPresheaf_class_of_field
    (K : Type u) [Field K] [CharZero K]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})
    (n : ℕ)
    (c : Sheaf.H'.{u} F (n + 1) (Scheme.Etale.mk (𝟙 (Spec (.of K))))) :
    ∃ (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
      (f : finiteGaloisEtaleObject K E ⟶ Scheme.Etale.mk (𝟙 (Spec (.of K)))),
      (F.cohomologyPresheaf (n + 1)).map f.op c = 0 := by
  obtain ⟨V, f, _, _, hs, hc⟩ :=
    exists_finiteEtale_killing_cohomologyPresheaf_class_of_field K F n c
  let P : (Spec (.of K)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
    F.cohomologyPresheaf (n + 1)
  let S : Sieve (Scheme.Etale.mk (𝟙 (Spec (.of K)))) :=
    Presheaf.equalizerSieve (F := P) c 0
  have hS : S ∈ (Spec (.of K)).smallEtaleTopology _ := by
    have h : S ∈ ((Spec (.of K)).smallPretopology
        (P := show MorphismProperty Scheme.{u} from @Etale)
        (Q := show MorphismProperty Scheme.{u} from @Etale)).toGrothendieck _ := by
      apply (Scheme.mem_toGrothendieck_smallPretopology
        (P := show MorphismProperty Scheme.{u} from @Etale)
        (Q := show MorphismProperty Scheme.{u} from @Etale) _ S).mpr
      intro x
      obtain ⟨y, hy⟩ := hs x
      refine ⟨V, f, y, ?_, inferInstance, ?_⟩
      · change P.map f.op c = P.map f.op 0
        rw [map_zero]
        exact hc
      · have h : f.left ≫ 𝟙 (Spec (.of K)) = V.hom := f.w
        have hf : f.left = V.hom := (Category.comp_id f.left).symm.trans h
        rw [hf]
        exact hy
    rw [← Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
      (Spec (.of K)) (le_refl _)] at h
    exact h
  obtain ⟨E, g, hg⟩ := exists_finiteGalois_mem_covering_sieve_of_field K S hS
  refine ⟨E, g, ?_⟩
  change P.map g.op c = P.map g.op 0 at hg
  simpa only [map_zero] using hg

end EtaleCohomology
