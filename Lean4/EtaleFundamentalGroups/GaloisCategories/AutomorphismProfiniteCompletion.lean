/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Topology.Category.FinTopCat
import ClassFieldTheory.LocalClassFieldTheory.Infinite.ProfiniteCompletion

/-!
# The profinite completion of a topological group

This file proves Stacks Project, Tag `0BMU`: the automorphism group of the
forgetful functor on finite continuous actions of a topological group is its
profinite completion.
-/

universe u v

noncomputable section

open CategoryTheory Topology
open scoped FintypeCatDiscrete PreGaloisCategory

namespace CategoryTheory

namespace FiniteContinuousAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private instance carrierMulAction
    (X : ContAction FintypeCat.{u} G) :
    MulAction G
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) :=
  inferInstanceAs <| MulAction G X.obj.V

private instance carrierContinuousSMul
    (X : ContAction FintypeCat.{u} G) :
    ContinuousSMul G
      ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X) := by
  change ContinuousSMul G
    ((forget₂ (Action FintypeCat.{u} G) TopCat).obj X.obj)
  exact X.property

private instance naturalSMul :
    PreGaloisCategory.IsNaturalSMul
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G where
  naturality g {X Y} f x := by
    change
      ConcreteCategory.hom (InducedCategory.Hom.hom f).hom
          (ConcreteCategory.hom (X.obj.ρ g) x) =
        ConcreteCategory.hom (Y.obj.ρ g)
          (ConcreteCategory.hom (InducedCategory.Hom.hom f).hom x)
    simpa only [FintypeCat.comp_apply] using
      ConcreteCategory.congr_hom ((InducedCategory.Hom.hom f).comm g) x

private theorem continuous_of_isOpen_ker
    {H : Type u} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (hf : IsOpen (f.ker : Set G)) :
    Continuous f := by
  apply continuous_of_continuousAt_one
  rw [continuousAt_def, map_one]
  intro A hA
  rw [mem_nhds_iff]
  refine ⟨f.ker, ?_, hf, f.ker.one_mem⟩
  intro g hg
  have h1 : (1 : H) ∈ A := mem_of_mem_nhds hA
  simpa only [Set.mem_preimage, MonoidHom.mem_ker.mp hg] using h1

private theorem canonicalHom_continuous :
    Continuous
      (PreGaloisCategory.toAut
        (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G) := by
  let F := forget₂ (ContAction FintypeCat.{u} G) FintypeCat
  let ρ := PreGaloisCategory.toAut F G
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding F).isInducing,
    continuous_pi_iff]
  intro X
  let ev : G →* Aut (F.obj X) :=
    (Pi.evalMonoidHom (fun Y : ContAction FintypeCat.{u} G ↦
      Aut (F.obj Y)) X).comp
        ((PreGaloisCategory.autEmbedding F).comp ρ)
  have hker :
      (ev.ker : Set G) =
        ⋂ x : F.obj X, (MulAction.stabilizer G x : Set G) := by
    ext g
    simp only [Set.mem_iInter]
    constructor
    · intro hg x
      change ev g = 1 at hg
      change g • x = x
      have happ := congrArg (fun a : Aut (F.obj X) ↦ a.hom x) hg
      change (ρ g).hom.app X x = x at happ
      simpa only [ρ, PreGaloisCategory.toAut_hom_app_apply] using happ
    · intro hg
      change ev g = 1
      apply Aut.ext
      ext x
      have hx := hg x
      change g • x = x at hx
      change (ρ g).hom.app X x = x
      simpa only [ρ, PreGaloisCategory.toAut_hom_app_apply] using hx
  have hopen : IsOpen (ev.ker : Set G) := by
    rw [hker]
    exact isOpen_iInter_of_finite fun x ↦ stabilizer_isOpen G x
  change Continuous ev
  exact continuous_of_isOpen_ker G ev hopen

omit [IsTopologicalGroup G] in
private theorem actionKernel_isOpen
    (X : ContAction FintypeCat.{u} G) :
    IsOpen
      ((MulAction.toPermHom G
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X)).ker :
          Set G) := by
  let S := (forget₂ (ContAction FintypeCat.{u} G) FintypeCat).obj X
  let a : G →* Equiv.Perm S := MulAction.toPermHom G S
  have hker :
      (a.ker : Set G) =
        ⋂ x : S, (MulAction.stabilizer G x : Set G) := by
    ext g
    simp only [Set.mem_iInter]
    constructor
    · intro hg x
      change a g = 1 at hg
      change g • x = x
      have hx := congrArg (fun e : Equiv.Perm S ↦ e x) hg
      change g • x = x at hx
      exact hx
    · intro hg
      change a g = 1
      ext x
      have hx := hg x
      change g • x = x at hx
      change g • x = x
      exact hx
  change IsOpen (a.ker : Set G)
  rw [hker]
  exact isOpen_iInter_of_finite fun x ↦ stabilizer_isOpen G x

private theorem quotient_continuousSMul
    (K : Subgroup G) [K.Normal]
    [TopologicalSpace (G ⧸ K)] [DiscreteTopology (G ⧸ K)]
    (hK : IsOpen (K : Set G)) :
    ContinuousSMul G (G ⧸ K) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K q
  convert hK using 1
  ext g
  change g • (QuotientGroup.mk a : G ⧸ K) =
      QuotientGroup.mk a ↔ g ∈ K
  constructor
  · intro hg
    change (QuotientGroup.mk g : G ⧸ K) * QuotientGroup.mk a =
      QuotientGroup.mk a at hg
    have hq : (QuotientGroup.mk g : G ⧸ K) = 1 := by
      exact mul_right_cancel (by simpa only [one_mul] using hg)
    exact (QuotientGroup.eq_one_iff g).mp hq
  · intro hg
    have hq : (QuotientGroup.mk g : G ⧸ K) = 1 :=
      (QuotientGroup.eq_one_iff g).mpr hg
    change (QuotientGroup.mk g : G ⧸ K) * QuotientGroup.mk a =
      QuotientGroup.mk a
    rw [hq, one_mul]

private theorem exists_canonicalHom_eq_on_finite
    {ι : Type v} [Finite ι]
    (X : ι → ContAction FintypeCat.{u} G)
    (σ : Aut
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat)) :
    ∃ g : G, ∀ i,
      (PreGaloisCategory.toAut
          (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G g).hom.app
          (X i) =
        σ.hom.app (X i) := by
  let F := forget₂ (ContAction FintypeCat.{u} G) FintypeCat
  let ρ := PreGaloisCategory.toAut F G
  let K : Subgroup G :=
    ⨅ i, (MulAction.toPermHom G (F.obj (X i))).ker
  have hKnormal : K.Normal := by
    dsimp only [K]
    exact Subgroup.normal_iInf_normal fun i ↦ inferInstance
  have hKfinite : K.FiniteIndex := by
    dsimp only [K]
    apply Subgroup.finiteIndex_iInf
    intro i
    exact Subgroup.finiteIndex_ker
      (MulAction.toPermHom G (F.obj (X i)))
  have hKopen : IsOpen (K : Set G) := by
    change IsOpen
      ((↑(⨅ i, (MulAction.toPermHom G (F.obj (X i))).ker) : Set G))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i ↦ actionKernel_isOpen G (X i)
  let : K.Normal := hKnormal
  let : K.FiniteIndex := hKfinite
  let : Fintype (G ⧸ K) := Subgroup.fintypeQuotientOfFiniteIndex
  let : TopologicalSpace (G ⧸ K) := ⊥
  let : DiscreteTopology (G ⧸ K) := ⟨rfl⟩
  let A : Action FintypeCat.{u} G :=
    Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ K))
  let Q : ContAction FintypeCat.{u} G :=
    ⟨A, by
      exact quotient_continuousSMul G K hKopen⟩
  obtain ⟨g, hg⟩ :=
    QuotientGroup.mk'_surjective K
      (σ.hom.app Q (1 : G ⧸ K))
  refine ⟨g, fun i ↦ ?_⟩
  ext x
  have hKle : K ≤ MulAction.stabilizer G x := by
    intro k hk
    have hki := Subgroup.mem_iInf.mp hk i
    change (MulAction.toPermHom G (F.obj (X i))) k = 1 at hki
    change k • x = x
    have hx := congrArg (fun e : Equiv.Perm (F.obj (X i)) ↦ e x) hki
    change k • x = x at hx
    exact hx
  let φfun : G ⧸ K → F.obj (X i) :=
    fun q ↦ Quotient.liftOn' q (fun a : G ↦ a • x) (by
      intro a b hab
      have hk : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
      have hfix : (a⁻¹ * b) • x = x := by
        exact hKle hk
      calc
        a • x = a • ((a⁻¹ * b) • x) := congrArg (a • ·) hfix.symm
        _ = b • x := by rw [smul_smul, mul_inv_cancel_left])
  have φfun_smul (a : G) (q : G ⧸ K) :
      φfun (a • q) = a • φfun q := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective K q
    exact mul_smul a b x
  let φAction : Q.obj ⟶ (X i).obj :=
    { hom := FintypeCat.homMk φfun
      comm := fun a ↦ by
        ext q
        exact φfun_smul a q }
  let φ : Q ⟶ X i := ObjectProperty.homMk φAction
  have hnat :=
    ConcreteCategory.congr_hom (σ.hom.naturality φ)
      (1 : G ⧸ K)
  have hφ_apply (q : G ⧸ K) :
      ConcreteCategory.hom (F.map φ) q = φfun q := rfl
  have hnat' :
      σ.hom.app (X i) (φfun (1 : G ⧸ K)) =
        φfun (σ.hom.app Q (1 : G ⧸ K)) := by
    have hnat0 :
        σ.hom.app (X i)
            (ConcreteCategory.hom (F.map φ) (1 : G ⧸ K)) =
          ConcreteCategory.hom (F.map φ)
            (σ.hom.app Q (1 : G ⧸ K)) := by
      calc
        _ = ConcreteCategory.hom (F.map φ ≫ σ.hom.app (X i))
            (1 : G ⧸ K) :=
          (FintypeCat.comp_apply (F.map φ) (σ.hom.app (X i))
            (1 : G ⧸ K)).symm
        _ = ConcreteCategory.hom (σ.hom.app Q ≫ F.map φ)
            (1 : G ⧸ K) := hnat
        _ = _ := FintypeCat.comp_apply (σ.hom.app Q) (F.map φ)
          (1 : G ⧸ K)
    simp only [hφ_apply] at hnat0
    exact hnat0
  have hφone : φfun (1 : G ⧸ K) = x := by
    change (1 : G) • x = x
    exact one_smul G x
  change g • x = σ.hom.app (X i) x
  calc
    g • x = φfun (QuotientGroup.mk g) := rfl
    _ = φfun (σ.hom.app Q (1 : G ⧸ K)) := congrArg φfun hg
    _ = σ.hom.app (X i) (φfun (1 : G ⧸ K)) := hnat'.symm
    _ = σ.hom.app (X i) x :=
      congrArg (fun y ↦ σ.hom.app (X i) y) hφone

private theorem canonicalHom_denseRange :
    DenseRange
      (PreGaloisCategory.toAut
        (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G) := by
  let F := forget₂ (ContAction FintypeCat.{u} G) FintypeCat
  let ρ := PreGaloisCategory.toAut F G
  apply dense_iff_inter_open.mpr
  rintro U ⟨V, hV, hVU⟩ ⟨σ, hσ⟩
  rw [← hVU, Set.mem_preimage] at hσ
  rcases (isOpen_pi_iff.mp hV) _ hσ with ⟨J, hJopen, hJmem, hJsubset⟩
  obtain ⟨g, hg⟩ :=
    exists_canonicalHom_eq_on_finite G (fun j : J ↦ j.1) σ
  refine ⟨ρ g, ?_, ⟨g, rfl⟩⟩
  rw [← hVU]
  apply hJsubset
  intro X hX
  have heq :
      PreGaloisCategory.autEmbedding F (ρ g) X =
        PreGaloisCategory.autEmbedding F σ X := by
    apply Iso.ext
    exact hg ⟨X, hX⟩
  exact Set.mem_of_eq_of_mem heq (hJmem X hX).2

private def canonicalContinuousHom :
    G →ₜ*
      Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) where
  toMonoidHom :=
    PreGaloisCategory.toAut
      (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G
  continuous_toFun := canonicalHom_continuous G

private noncomputable def automorphismProfiniteGroup : ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of
    (Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat))

private theorem canonicalHom_preimage_cofinal
    (H : LocalClassFieldTheory.OpenFiniteIndexNormalSubgroup G) :
    ∃ N : OpenNormalSubgroup
        (Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat)),
      LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex
          (automorphismProfiniteGroup G)
          (canonicalContinuousHom G) N ≤ H := by
  let F := forget₂ (ContAction FintypeCat.{u} G) FintypeCat
  let K : Subgroup G := H.toOpenNormalSubgroup.toSubgroup
  let : K.Normal := H.toOpenNormalSubgroup.isNormal'
  let : K.FiniteIndex := H.finiteIndex'
  let : Fintype (G ⧸ K) := Subgroup.fintypeQuotientOfFiniteIndex
  let : TopologicalSpace (G ⧸ K) := ⊥
  let : DiscreteTopology (G ⧸ K) := ⟨rfl⟩
  let A : Action FintypeCat.{u} G :=
    Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ K))
  let Q : ContAction FintypeCat.{u} G :=
    ⟨A, by
      exact quotient_continuousSMul G K H.toOpenNormalSubgroup.isOpen'⟩
  let ev : Aut F →* Aut (F.obj Q) :=
    (Pi.evalMonoidHom
      (fun X : ContAction FintypeCat.{u} G ↦ Aut (F.obj X)) Q).comp
        (PreGaloisCategory.autEmbedding F)
  have hev : Continuous ev := by
    exact (continuous_apply Q).comp
      (PreGaloisCategory.autEmbedding_isClosedEmbedding F).continuous
  have hevKer : IsOpen (ev.ker : Set (Aut F)) := by
    change IsOpen (ev ⁻¹' ({1} : Set (Aut (F.obj Q))))
    exact (isOpen_discrete {1}).preimage hev
  let N : OpenNormalSubgroup (Aut F) :=
    { toOpenSubgroup :=
        { toSubgroup := ev.ker
          isOpen' := hevKer }
      isNormal' := by infer_instance }
  refine ⟨N, ?_⟩
  intro g hg
  change canonicalContinuousHom G g ∈ N at hg
  change ev (canonicalContinuousHom G g) = 1 at hg
  have hpoint :=
    congrArg (fun a : Aut (F.obj Q) ↦ a.hom (1 : G ⧸ K)) hg
  change g • (1 : G ⧸ K) = (1 : G ⧸ K) at hpoint
  change g ∈ H.toOpenNormalSubgroup.toSubgroup
  apply (QuotientGroup.eq_one_iff g).mp
  change (QuotientGroup.mk g : G ⧸ K) = 1
  change (QuotientGroup.mk g : G ⧸ K) * 1 = 1 at hpoint
  simpa only [mul_one] using hpoint

private theorem canonicalLift_injective :
    Function.Injective
      (LocalClassFieldTheory.topologicalProfiniteCompletionLift
        (automorphismProfiniteGroup G) (canonicalContinuousHom G)) := by
  let P := automorphismProfiniteGroup G
  let f := canonicalContinuousHom G
  change Function.Injective
    (LocalClassFieldTheory.topologicalProfiniteCompletionLift P f).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    change x = 1
    apply Subtype.ext
    funext H
    obtain ⟨N, hNH⟩ := canonicalHom_preimage_cofinal G H
    change OpenNormalSubgroup P at N
    let e := ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor P
    have hlimit :
        LocalClassFieldTheory.topologicalProfiniteCompletionToFiniteQuotientLimit
            P f x = 1 := by
      have he := congrArg e hx
      simpa [LocalClassFieldTheory.topologicalProfiniteCompletionLift, e] using he
    have hfinite :
        LocalClassFieldTheory.topologicalProfiniteCompletionFiniteProjection
            P f N x = 1 := by
      exact congrFun (congrArg Subtype.val hlimit) N
    have hpreimage :
        LocalClassFieldTheory.topologicalProfiniteCompletionProjection G
            (LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex
              P f N) x = 1 := by
      have hinjective : Function.Injective
          (LocalClassFieldTheory.topologicalProfiniteCompletionFiniteQuotientMorphism
            P f N) := by
        change Function.Injective
          (LocalClassFieldTheory.topologicalProfiniteCompletionFiniteQuotientMap
            P f N)
        apply (MonoidHom.ker_eq_bot_iff (M := P ⧸ (N : Subgroup P))
          (LocalClassFieldTheory.topologicalProfiniteCompletionFiniteQuotientMap
            P f N)).mp
        apply le_antisymm
        · intro q hq
          obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
            (LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex
              P f N).toOpenNormalSubgroup.toSubgroup q
          apply (QuotientGroup.eq_one_iff g).2
          change f g ∈ N
          exact (QuotientGroup.eq_one_iff (N := (N : Subgroup P)) (f g)).1 hq
        · exact bot_le
      change
        LocalClassFieldTheory.topologicalProfiniteCompletionFiniteQuotientMorphism
            P f N
            (LocalClassFieldTheory.topologicalProfiniteCompletionProjection G
              (LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex
                P f N) x) = 1 at hfinite
      apply hinjective
      simpa only [map_one] using hfinite
    let i :
        LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex
            P f N ⟶ H :=
      hNH.hom
    have htransition :=
      LocalClassFieldTheory.topologicalProfiniteCompletionProjection_transition
        G i x
    change
      LocalClassFieldTheory.topologicalProfiniteCompletionProjection G H x = 1
    exact htransition.symm.trans
      ((congrArg
        (fun y : LocalClassFieldTheory.openFiniteQuotient G
            (LocalClassFieldTheory.topologicalProfiniteCompletionPreimageIndex P f N) =>
          (LocalClassFieldTheory.openFiniteQuotientDiagram G).map i y)
        hpreimage).trans
        (map_one ((LocalClassFieldTheory.openFiniteQuotientDiagram G).map i).hom))
  · exact bot_le

private theorem canonicalLift_surjective :
    Function.Surjective
      (LocalClassFieldTheory.topologicalProfiniteCompletionLift
        (automorphismProfiniteGroup G) (canonicalContinuousHom G)) := by
  let lift :=
    LocalClassFieldTheory.topologicalProfiniteCompletionLift
      (automorphismProfiniteGroup G) (canonicalContinuousHom G)
  have hLiftDense : DenseRange lift := by
    intro y
    apply closure_mono
      (s := Set.range (canonicalContinuousHom G))
      (t := Set.range lift)
      ?_ ((canonicalHom_denseRange G) y)
    rintro z ⟨g, rfl⟩
    exact
      ⟨LocalClassFieldTheory.topologicalProfiniteCompletionMap G g,
        LocalClassFieldTheory.topologicalProfiniteCompletionLift_map
          (automorphismProfiniteGroup G) (canonicalContinuousHom G) g⟩
  have hclosed : IsClosed (Set.range lift) :=
    lift.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr hclosed]
  exact hLiftDense.closure_eq

/-- The automorphism group of the forgetful functor on finite continuous
`G`-sets is canonically the profinite completion of `G`. -/
@[stacks 0BMU]
noncomputable def profiniteCompletionEquivAutForget :
    LocalClassFieldTheory.TopologicalProfiniteCompletion G ≃ₜ*
      Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) := by
  let lift :=
    LocalClassFieldTheory.topologicalProfiniteCompletionLift
      (automorphismProfiniteGroup G)
      (canonicalContinuousHom G)
  have hliftSurjective : Function.Surjective lift :=
    canonicalLift_surjective G
  have hliftInjective : Function.Injective lift :=
    canonicalLift_injective G
  let e :=
    MulEquiv.ofBijective lift.toMonoidHom
      ⟨hliftInjective, hliftSurjective⟩
  exact
    { toMulEquiv := e
      continuous_toFun := lift.continuous_toFun
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          (f := e.toEquiv) lift.continuous_toFun }

@[simp]
theorem profiniteCompletionEquivAutForget_apply_completionMap
    (g : G) :
    profiniteCompletionEquivAutForget G
        (LocalClassFieldTheory.topologicalProfiniteCompletionMap G g) =
      PreGaloisCategory.toAut
        (forget₂ (ContAction FintypeCat.{u} G) FintypeCat) G g := by
  change
    LocalClassFieldTheory.topologicalProfiniteCompletionLift
        (automorphismProfiniteGroup G) (canonicalContinuousHom G)
        (LocalClassFieldTheory.topologicalProfiniteCompletionMap G g) =
      canonicalContinuousHom G g
  exact LocalClassFieldTheory.topologicalProfiniteCompletionLift_map
    (automorphismProfiniteGroup G)
    (canonicalContinuousHom G) g

end FiniteContinuousAction

end CategoryTheory
