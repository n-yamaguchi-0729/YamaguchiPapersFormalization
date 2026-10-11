/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Extensions
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Fibers of extensions of étale abelian sheaves

The inverse image of a global section of the quotient of a short exact
sequence is an actual sheaf of sets. It has sections étale locally, and any
section identifies that fiber with the kernel by translation. These are the
local torsor constructions for the comparison with degree-one cohomology.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ S.X₃.obj ⋙ forget AddCommGrpCat.{u})

private lemma section_naturality {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    S.X₃.obj.map f (t.app U PUnit.unit) = t.app V PUnit.unit := by
  exact (ConcreteCategory.congr_hom (t.naturality f) PUnit.unit).symm

/-- The sectionwise fiber of the quotient map over a global section. -/
abbrev extensionFiberSubfunctor : Subfunctor (S.X₂.obj ⋙ forget AddCommGrpCat.{u}) where
  obj U := {e | S.g.hom.app U e = t.app U PUnit.unit}
  map {U V} f e he := by
    change S.g.hom.app V (S.X₂.obj.map f e) = t.app V PUnit.unit
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f) e
    change S.g.hom.app V (S.X₂.obj.map f e) =
      S.X₃.obj.map f (S.g.hom.app U e) at hn
    exact hn.trans ((congrArg (S.X₃.obj.map f) he).trans (section_naturality S t f))

/-- Equality with a fixed quotient section is local, so the sectionwise fiber
is a sheaf, not merely a presheaf. -/
theorem extensionFiber_isSheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (extensionFiberSubfunctor S t).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  have hE : Presieve.IsSheaf X.smallEtaleTopology (S.X₂.obj ⋙ forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₂).property
  have hZ : Presieve.IsSheaf X.smallEtaleTopology (S.X₃.obj ⋙ forget AddCommGrpCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})).obj S.X₃).property
  apply (Subfunctor.isSheaf_iff _ hE).mpr
  intro U e hcov
  change S.g.hom.app U e = t.app U PUnit.unit
  apply (hZ _ hcov).isSeparatedFor.ext
  intro V f hf
  change S.X₃.obj.map f.op (S.g.hom.app U e) =
    S.X₃.obj.map f.op (t.app U PUnit.unit)
  have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) e
  change S.g.hom.app (op V) (S.X₂.obj.map f.op e) =
    S.X₃.obj.map f.op (S.g.hom.app U e) at hn
  exact hn.symm.trans (hf.trans (section_naturality S t f.op).symm)

/-- The actual étale sheaf obtained as the inverse image of the quotient section. -/
abbrev extensionFiber : Sheaf X.smallEtaleTopology (Type u) :=
  ⟨(extensionFiberSubfunctor S t).toFunctor, extensionFiber_isSheaf S t⟩

/-- Every quotient section of a short exact sequence lifts on an étale cover. -/
theorem extensionFiber_locally_nonempty (hS : S.ShortExact) (U : X.Etaleᵒᵖ) :
    Presheaf.imageSieve S.g.hom (t.app U PUnit.unit) ∈ X.smallEtaleTopology U.unop := by
  have : Epi S.g := hS.epi_g
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr inferInstance
  exact Presheaf.imageSieve_mem X.smallEtaleTopology S.g.hom (t.app U PUnit.unit)

private lemma sections_exact (hS : S.ShortExact) (U : X.Etaleᵒᵖ) :
    (S.map ((sheafSections X.smallEtaleTopology AddCommGrpCat).obj U)).Exact :=
  by
  let Γ := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj U
  exact hS.exact.map_of_mono_of_preservesKernel Γ hS.mono_f inferInstance

/-- Translation by a chosen lift is bijective from the kernel sections to the
fiber. The inverse is supplied by the actual kernel universal property. -/
theorem extensionFiber_translation_bijective (hS : S.ShortExact) (U : X.Etaleᵒᵖ)
    (e : {b : S.X₂.obj.obj U // S.g.hom.app U b = t.app U PUnit.unit}) :
    Function.Bijective (fun a : S.X₁.obj.obj U =>
      (⟨S.f.hom.app U a + e.val, by
        rw [map_add]
        have hz := ConcreteCategory.congr_hom
          (congrArg (fun k : S.X₁ ⟶ S.X₃ => k.hom.app U) S.zero) a
        change S.g.hom.app U (S.f.hom.app U a) = 0 at hz
        rw [hz, zero_add]
        exact e.property⟩ : {b : S.X₂.obj.obj U // S.g.hom.app U b = t.app U PUnit.unit})) := by
  have : Mono S.f := hS.mono_f
  have hm : Mono (S.f.hom.app U) := inferInstance
  have hi := (AddCommGrpCat.mono_iff_injective (S.f.hom.app U)).mp hm
  constructor
  · intro a b hab
    exact hi (add_right_cancel (congrArg Subtype.val hab))
  · intro z
    have hz : S.g.hom.app U (z.val - e.val) = 0 := by
      rw [map_sub, z.property, e.property, sub_self]
    obtain ⟨a, ha⟩ :=
      (ShortComplex.ab_exact_iff _).mp (sections_exact S hS U) (z.val - e.val) hz
    refine ⟨a, Subtype.ext ?_⟩
    change S.f.hom.app U a + e.val = z.val
    exact (congrArg (fun q => q + e.val) ha).trans (sub_add_cancel z.val e.val)

end EtaleFundamentalGroups.Cohomology
