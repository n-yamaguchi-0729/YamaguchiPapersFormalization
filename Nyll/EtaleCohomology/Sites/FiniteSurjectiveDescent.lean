/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.FiniteCechStalkLift
import Nyll.EtaleCohomology.Sites.FinitePushforwardStalks
import Nyll.EtaleCohomology.Sites.FiniteSurjectiveUnit
import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
import Nyll.EtaleCohomology.Sites.SectionImageGluing
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Descent of sections along arbitrary finite surjections

Čech-compatible sections give germs downstairs. Injectivity of the actual
finite direct-image stalk comparison puts the direct-image section in the
unit's image on every stalk. The unit is a monomorphism, so these local
preimages glue uniquely.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

private theorem exists_global_lift_of_geometricStalk_range
    {X : Scheme.{u}} (Λ : Type u) [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)} (η : F ⟶ G) [Mono η]
    (a : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (ha : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ X),
      ∃ b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj F),
        (Scheme.pointSmallEtale t).sheafFiber.map η b = etaleGlobalSectionsGerm t Λ G a) :
    ∃ b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      η.hom.app (op (Scheme.Etale.mk (𝟙 X))) b = a := by
  classical
  let X₀ : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hlocal (x : X) : ∃ (V : X.Etale) (g : V ⟶ X₀) (v : V.left),
      (Presheaf.imageSieve η.hom a) g ∧ g.left v = x := by
    let Ω : Type u := AlgebraicClosure (X.residueField x)
    let t : Spec (CommRingCat.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫
        X.fromSpecResidueField x
    have ht : t default = x := by
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply x _
    let Φ := Scheme.pointSmallEtale t
    let u₀ : Φ.fiber.obj X₀ := Over.homMk t (Category.comp_id t)
    obtain ⟨b, hb⟩ := ha Ω t
    obtain ⟨V, v, c, hc⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) b
    let g : V ⟶ X₀ := MorphismProperty.Over.homMk
      (P := show MorphismProperty Scheme.{u} from @Etale) (Q := ⊤)
      V.hom (Category.comp_id V.hom)
    have hg : Φ.fiber.map g v = u₀ := by
      apply Over.OverMorphism.ext
      exact v.w
    have hgc : Φ.toPresheafFiber V v G.obj (η.hom.app (op V) c) =
        Φ.toPresheafFiber V v G.obj (G.obj.map g.op a) := by
      refine (Φ.toPresheafFiber_naturality_apply η.hom V v c).symm.trans ?_
      refine ((congrArg (Φ.presheafFiber.map η.hom) hc).trans hb).trans ?_
      exact (ConcreteCategory.congr_hom
        ((Φ.toPresheafFiber_w g v G.obj).trans
          (congrArg (fun z => Φ.toPresheafFiber X₀ z G.obj) hg)) a).symm
    obtain ⟨W, h, w, _, hcw⟩ :=
      (Φ.toPresheafFiber_eq_iff' (P := G.obj) V v _ _).mp hgc
    let j : W ⟶ X₀ := h ≫ g
    have hj : j.left = W.hom :=
      (Category.comp_id j.left).symm.trans j.w
    refine ⟨W, j, w.left (default : Spec (CommRingCat.of Ω)), ?_, ?_⟩
    · refine ⟨F.obj.map h.op c, ?_⟩
      refine (NatTrans.naturality_apply η.hom h.op c).trans ?_
      refine hcw.trans ?_
      exact (G.obj.map_comp_apply g.op h.op a).symm
    · refine (congrArg (fun k : W.left ⟶ X =>
        k (w.left (default : Spec (CommRingCat.of Ω)))) hj).trans ?_
      exact (Scheme.Hom.comp_apply w.left W.hom (default : Spec (CommRingCat.of Ω))).symm.trans
        ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ X => k default) w.w).trans ht)
  choose V g v hg hv using hlocal
  have hcover : Sieve.ofArrows V g ∈ X.smallEtaleTopology X₀ := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, v x, hv x⟩
  have himage : Presheaf.imageSieve η.hom a ∈ X.smallEtaleTopology X₀ := by
    apply X.smallEtaleTopology.superset_covering (R := Presheaf.imageSieve η.hom a) ?_ hcover
    intro W j hj
    obtain ⟨x, k, rfl⟩ := (Sieve.mem_ofArrows_iff V g j).mp hj
    exact (Presheaf.imageSieve η.hom a).downward_closed (hg x) k
  have : Mono η.hom := inferInstanceAs (Mono ((sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u} Λ)).map η))
  let η₀ := (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u} Λ))).map η
  exact Sites.exists_section_lift_of_imageSieve_mem η₀
    (fun U => (ModuleCat.mono_iff_injective (η.hom.app U)).mp inferInstance) a himage

/-- Pullback of global sections is injective along a finite surjection. -/
theorem etaleFiniteSurjective_globalSections_injective
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    Function.Injective (etalePullbackGlobalSectionsMap q Λ F) := by
  let η : F ⟶ (etalePushforward q Λ).obj ((etalePullback q Λ).obj F) :=
    (etalePullbackPushforwardAdjunction q Λ).unit.app F
  have : Mono η := etaleFiniteSurjective_unit_mono q Λ F
  have : Mono η.hom := inferInstanceAs (Mono ((sheafToPresheaf X.smallEtaleTopology
    (ModuleCat.{u} Λ)).map η))
  rw [← etalePullbackGlobalSectionsMap_eq_unit]
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Every global section of inverse image satisfying the actual Čech equation
descends uniquely along an arbitrary finite surjection of schemes. -/
theorem existsUnique_globalSections_lift_of_finite_cech_compatible
    {X Y : Scheme.{u}} (q : Y ⟶ X) [IsFinite q] [Surjective q]
    (Λ : Type u) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (a : ((etalePullback q Λ).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))))
    (ha : etaleCechFirstSectionsMap q Λ F a = etaleCechSecondSectionsMap q Λ F a) :
    ∃! b : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))),
      etalePullbackGlobalSectionsMap q Λ F b = a := by
  let Fq := (etalePullback q Λ).obj F
  let G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) := (etalePushforward q Λ).obj Fq
  let η : F ⟶ G := (etalePullbackPushforwardAdjunction q Λ).unit.app F
  have : Mono η := etaleFiniteSurjective_unit_mono q Λ F
  let e := etalePushforwardGlobalSectionsIso q Λ Fq
  let a' : G.obj.obj (op (Scheme.Etale.mk (𝟙 X))) := e.inv a
  have hea : e.hom a' = a := ConcreteCategory.congr_hom e.inv_hom_id a
  have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ X) :
      ∃ b : ToType ((Scheme.pointSmallEtale t).sheafFiber.obj F),
        (Scheme.pointSmallEtale t).sheafFiber.map η b = etaleGlobalSectionsGerm t Λ G a' := by
    obtain ⟨b, hb⟩ := exists_stalk_lift_of_finite_cech_compatible q t Λ F a ha
    refine ⟨b, ?_⟩
    apply etalePushforwardStalkComponents_jointly_injective q t Fq
    intro s
    refine (hb s).trans ?_
    have h := ConcreteCategory.congr_hom (etalePushforwardGlobalSectionsIso_germ q Λ t s Fq) a'
    exact (congrArg (etaleGlobalSectionsGerm s.val Λ Fq) hea).symm.trans h.symm
  obtain ⟨b, hb⟩ := exists_global_lift_of_geometricStalk_range Λ η a' hstalk
  have hunit := etalePullbackGlobalSectionsMap_eq_unit q Λ F
  have hmap : etalePullbackGlobalSectionsMap q Λ F b = a :=
    (ConcreteCategory.congr_hom hunit b).symm.trans ((congrArg e.hom hb).trans hea)
  exact ⟨b, hmap, fun c hc =>
    etaleFiniteSurjective_globalSections_injective q Λ F (hc.trans hmap.symm)⟩

end EtaleCohomology
