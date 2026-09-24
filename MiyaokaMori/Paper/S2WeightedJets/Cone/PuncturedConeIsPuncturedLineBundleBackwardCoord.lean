import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackwardThetaW
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractInjective
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedTautologicalSectionFrame
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveFactorEquationVanishes
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ConeMorphismScaleOfCoordinatesHelpers
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.Stacks01ne

/-! # Coordinates `z'` of `Tot(L)^×` over `C` and their two properties

Part of the construction of the backward morphism `β : Tot(L)^× → Z^×` (module
`…PuncturedConeIsPuncturedLineBundleBackward`, which imports this one). Notation as there:
`T× := Tot(L)^×`, `π := totalSpacePunctured.toBase L`, `t' := base = π ≫ pr₁`, `x' := toX = π ≫ pr₂`,
`w := tautologicalSection L`, `q_i := pr₂^*(e^*x_i)`, `z_i := coordZ = ⟨w, π^*q_i⟩`, `z'_i := coord` (its transport to
`Γ(T×, t'^*A)`).

* `theta : x'^*O_X(1) ≅ t'^*A` is `θ_w` (module `…BackwardThetaW`) conjugated by the `pullbackComp` transports;
  `theta_hom_app`: `θ(x'^*(e^*x_i)) = z'_i`.
* `coord_nowhereZero`: `θ` is an isomorphism and the `x'^*(e^*x_i)`
  are nowhere all zero (`exists_not_isZeroAt_coordinate`, from Stacks 01NE: the `x_i` generate `O_{P^N}(1)`).
* `projectivizationMorphism_coord_eq`: `x' ≫ e.emb` is the projectivization of the tuple `z'` (Stacks 01NE,
  `projectiveSpace_hom_ext_of_sections` with `θ`).
* `eval_coord_eq_zero`: `F_j(z') = 0` because the projectivization of
  `z'` factors through `X` (`evalHomogeneousAtSections_eq_zero_of_projectivization_factors`).

Source: eq. (2.1) of the paper. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Evaluating a composite of two isomorphisms on a global section (definitional). -/
theorem Iso.trans_hom_val_app_apply {M N P : X.Modules} (α : M ≅ N) (β : N ≅ P)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((α ≪≫ β).hom.val.app (Opposite.op ⊤)).hom x =
      (β.hom.val.app (Opposite.op ⊤)).hom ((α.hom.val.app (Opposite.op ⊤)).hom x) := rfl

/-- `α.inv.app M` after `α.hom.app M` is the identity on global sections. -/
theorem natIso_inv_hom_val_app {Y : AlgebraicGeometry.Scheme.{u}} {F G : Y.Modules ⥤ X.Modules} (α : F ≅ G)
    (M : Y.Modules) (y : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((α.inv.app M).val.app (Opposite.op ⊤)).hom (((α.hom.app M).val.app (Opposite.op ⊤)).hom y)) = y :=
  congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom y) (α.hom_inv_id_app M)

/-- The `(θ.hom.app ⊤).hom x` spelling of `projectiveSpace_hom_ext_of_sections` versus `.val.app` (definitional). -/
theorem Hom.app_hom_eq_val_app {M N : X.Modules} (φ : M ⟶ N) (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (φ.app ⊤).hom x = (φ.val.app (Opposite.op ⊤)).hom x := rfl

end AlgebraicGeometry.Scheme.Modules

namespace puncturedTotalSpaceToCone

variable {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]

/-! ## Notation -/

/-- `t' : Tot(L)^× → C`, the base point: `π ≫ pr₁`. -/
def base : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶ C :=
  AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A) ≫
    CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- `x' : Tot(L)^× → X`: `π ≫ pr₂`. -/
def toX : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme ⟶ X :=
  AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A) ≫
    CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

set_option warn.classDefReducibility false in
/-- The `k`-structure of `Tot(L)^×`: `t' ≫ (C ↘ Spec k)`. **Not a global instance** (same convention as
`puncturedConeToProduct.overK`); introduce it locally with `letI`. -/
def overK : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme.Over
    (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨base e A ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

/-- `z_i := ⟨w, π^*q_i⟩ ∈ Γ(Tot(L)^×, π^*pr₁^*A)`: the pairing of the tautological section with the pulled-back
coordinate `pr₂^*(e^*x_i)`. This is the right-hand side of the coordinate identity in `IsTotalSpaceToConeHom`. -/
def coordZ (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)).val.obj (Opposite.op ⊤) : Type u) :=
  conePuncturedLineBundle.contractSections e A
    (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)))
    (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A))
    (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (conePuncturedLineBundle.coordinate C e i))

/-- `z'_i ∈ Γ(Tot(L)^×, t'^*A)`: `z_i` transported along `pullbackComp π pr₁ : π^*pr₁^* ≅ (π ≫ pr₁)^* = t'^*`. -/
def coord (i : Fin (N + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A).val.obj (Opposite.op ⊤) : Type u) :=
  (((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app A).val.app (Opposite.op ⊤)).hom
    (coordZ e A i)

/-! ## `θ : x'^*O_X(1) ≅ t'^*A` -/

/-- The tautological section `w` is a global frame of `π^*L` (`PuncturedTautologicalSectionFrame`, in the
spelling `toBase`/`tautologicalSection`). -/
theorem tautologicalSection_isFrame :
    AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))).obj
        (conePuncturedLineBundle e A)) ⊤
      (AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection (conePuncturedLineBundle e A)) :=
  AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_isFrame (conePuncturedLineBundle e A)

/-- `θ : x'^*O_X(1) ≅ t'^*A`: `θ_w` (`conePuncturedLineBundle.thetaW`, the pairing with the tautological frame `w`)
conjugated by the transports `pullbackComp π pr₂ : π^*pr₂^* ≅ x'^*` and `pullbackComp π pr₁ : π^*pr₁^* ≅ t'^*`. -/
def theta :
    (AlgebraicGeometry.Scheme.Modules.pullback (toX e A)).obj (e.oX 1) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).app
      (e.oX 1)).symm ≪≫
    conePuncturedLineBundle.thetaW e A
      (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)))
      (tautologicalSection_isFrame e A) ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).app A

/-- `(pullbackComp π pr₂)⁻¹ (x'^*(e^*x_i)) = π^*q_i`. -/
theorem pullbackComp_inv_coordinate (i : Fin (N + 1)) :
    ((((AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).inv.app
      (e.oX 1)).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (M := e.oX 1) (toX e A) (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i)))) =
    sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (conePuncturedLineBundle.coordinate C e i) := by
  have h := sectionPullbackAlong_comp (M := e.oX 1)
    (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
    (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i))
  have h2 := AlgebraicGeometry.Scheme.Modules.natIso_inv_hom_val_app
    (AlgebraicGeometry.Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    (e.oX 1)
    (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (sectionPullbackAlong (M := e.oX 1)
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
        (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i))))
  rw [h] at h2
  exact h2

/-- `θ(x'^*(e^*x_i)) = z'_i`. -/
theorem theta_hom_app (i : Fin (N + 1)) :
    ((theta e A).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (M := e.oX 1) (toX e A) (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i))) =
    coord e A i := by
  have h2 := conePuncturedLineBundle.thetaW_hom_app e A (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)))
    (tautologicalSection_isFrame e A) (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle.coordinate C e i))
  have h3 : (((conePuncturedLineBundle.thetaW e A (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)))
      (tautologicalSection_isFrame e A)).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (conePuncturedLineBundle.coordinate C e i))) = coordZ e A i := h2
  exact (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app A).val.app
      (Opposite.op ⊤)).hom
      (((conePuncturedLineBundle.thetaW e A (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))) (tautologicalSection_isFrame e A)).hom.val.app
        (Opposite.op ⊤)).hom z)) (pullbackComp_inv_coordinate e A i)).trans
    (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app A).val.app
      (Opposite.op ⊤)).hom z) h3)

/-! ## Leaf 1: the coordinates `z'` are nowhere all zero -/

/-- **`z'_0, …, z'_N` are nowhere all zero.**

Source: eq. (2.1) of the paper ("`z_i = θ_w(x^*x_i)`, and the `x_i` generate `O(1)`"); Stacks 01CT
(`contract` is an isomorphism), Stacks 01NE (the `x_i` are nowhere all zero on `P^N`).

Proof: `z'_i = θ(x'^*(e^*x_i))` (`theta_hom_app`) with `θ` an isomorphism, so `IsZeroAt` transfers
(`isZeroAt_iso_iff`); `x'^*(e^*x_i)` is the transport of `π^*(pr₂^*(e^*x_i))` along `pullbackComp`, and for every
point some `π^*(pr₂^*(e^*x_i))` is nonzero there (`exists_not_isZeroAt_coordinate`). Edge case `T× = ∅`: vacuous. -/
theorem coord_nowhereZero :
    ∀ y : (AlgebraicGeometry.Scheme.totalSpacePunctured (conePuncturedLineBundle e A)).toScheme,
      ∃ i, ¬ IsZeroAt (coord e A i) y := by
  intro y
  obtain ⟨i, hi⟩ := conePuncturedLineBundle.exists_not_isZeroAt_coordinate e
    (CategoryTheory.Over.mk (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))) y
  refine ⟨i, ?_⟩
  rw [← theta_hom_app e A i, AlgebraicGeometry.Scheme.Modules.isZeroAt_iso_iff']
  have h : sectionPullbackAlong (M := e.oX 1) (toX e A) (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i)) =
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).hom.app
        (e.oX 1)).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
          (conePuncturedLineBundle.coordinate C e i))) :=
    (sectionPullbackAlong_comp (M := e.oX 1)
      (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A))
      (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i))).symm
  rw [h]
  exact fun hz => hi ((AlgebraicGeometry.Scheme.Modules.isZeroAt_iso_iff'
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase (conePuncturedLineBundle e A)) (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).app (e.oX 1))
    _ y).mp hz)

/-! ## `x' ≫ e.emb` is the projectivization of `z'` -/

/-- `x' ≫ e.emb : Tot(L)^× → P^N` is a `k`-morphism for the `k`-structure `overK`: both `t' ≫ (C ↘ Spec k)` and
`x' ≫ (X ↘ Spec k)` are `π ≫ (C ×_k X ↘ Spec k)` (`pullback.condition`), and `e.emb` is a `k`-morphism (`e.over`). -/
theorem toX_comp_emb_isOver :
    letI := overK e A
    (toX e A ≫ e.emb).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  letI := overK e A
  refine ⟨?_⟩
  show (toX e A ≫ e.emb) ≫ (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
    base e A ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  rw [Category.assoc, e.over]
  unfold toX base
  rw [Category.assoc, Category.assoc, CategoryTheory.Limits.pullback.condition]

/-- **`x' ≫ e.emb` is the projectivization morphism of the tuple `z'`** (Stacks 01NE,
`projectiveSpace_hom_ext_of_sections`): the isomorphism `(x' ≫ e.emb)^*O(1) ≅ x'^*(e^*O(1)) ≅ t'^*A`
(`pullbackComp`, then `θ`) sends `(x' ≫ e.emb)^*x_i` to `θ(x'^*(e^*x_i)) = z'_i` (`theta_hom_app`). -/
theorem projectivizationMorphism_coord_eq :
    letI := overK e A
    projectivizationMorphism (k := k) ((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A)
      (coord e A) (coord_nowhereZero e A) = toX e A ≫ e.emb := by
  letI := overK e A
  haveI := toX_comp_emb_isOver e A
  symm
  refine projectiveSpace_hom_ext_of_sections (toX e A ≫ e.emb) _ (coord e A) (coord_nowhereZero e A)
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp (toX e A) e.emb).app (projectiveSpaceTwist k N 1)).symm ≪≫
      theta e A) ?_
  intro i
  -- The inner term of `coordinate C e i` is `sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i)`,
  -- definitionally equal to the right-hand side.
  have hcs : sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i) =
      sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i) := rfl
  have h2 := AlgebraicGeometry.Scheme.Modules.natIso_inv_hom_val_app
    (AlgebraicGeometry.Scheme.Modules.pullbackComp (toX e A) e.emb) (projectiveSpaceTwist k N 1)
    (sectionPullbackAlong (toX e A) (sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i)))
  rw [sectionPullbackAlong_comp (toX e A) e.emb (projectiveSpaceCoordinate k N i)] at h2
  have h3 : sectionPullbackAlong (toX e A) (sectionPullbackAlong e.emb (projectiveSpaceCoordinate k N i)) =
      sectionPullbackAlong (M := e.oX 1) (toX e A) (sectionPullbackAlong (M := projectiveSpaceTwist k N 1) e.emb (projectiveSpaceCoordinate k N i)) :=
    (congrArg (sectionPullbackAlong (toX e A)) hcs).symm
  exact (congrArg (fun z => ((theta e A).hom.val.app (Opposite.op ⊤)).hom z) (h2.trans h3)).trans
    (theta_hom_app e A i)

/-! ## Leaf 2: the equations of `X` vanish on `z'` -/

/-- **`F_j(z'_0, …, z'_N) = 0`** for every defining equation `F_j` of `X ⊆ P^N`
(`k`-structure `overK` on `Tot(L)^×`).

Source: eq. (2.1) of the paper (`F_j(z) = F_j(θ_w(x^*x)) = θ_w^{⊗d}(x^*F_j(x)) = 0`);
the vanishing ideal of `X` (`EmbeddingEquations.spans`).

Proof: the projectivization of the tuple `z'` is `x' ≫ e.emb` (`projectivizationMorphism_coord_eq`), i.e. it factors
through `X`; hence every homogeneous `F` in the vanishing ideal of `X` satisfies `F(z') = 0`
(`evalHomogeneousAtSections_eq_zero_of_projectivization_factors`), and `F_j` lies in that ideal by `E.spans`. -/
theorem eval_coord_eq_zero :
    letI := overK e A
    ∀ j, evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback (base e A)).obj A)
      (E.F j) (E.homogeneous j) (coord e A) = 0 := by
  letI := overK e A
  intro j
  apply evalHomogeneousAtSections_eq_zero_of_projectivization_factors e (toX e A) _ (coord e A)
    (coord_nowhereZero e A) (projectivizationMorphism_coord_eq e A) (E.F j) (E.homogeneous j)
  rw [← E.spans]
  exact Ideal.subset_span ⟨j, rfl⟩

end puncturedTotalSpaceToCone

end
