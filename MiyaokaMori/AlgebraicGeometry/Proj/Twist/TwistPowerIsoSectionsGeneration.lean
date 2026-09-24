import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear

/-! # Sufficient divisibility passes from the sheaf to the section rings

Sufficient divisibility of a graded quasi-coherent algebra at the sheaf level (`GradedQCAlgebra.SufficientlyDivisible`)
implies sufficient divisibility of the associated graded affine algebra of section rings
(`GradedAffineAlgebra.SufficientlyDivisible`): `SufficientlyDivisible.toGradedAffineAlgebra`.

Sources: Stacks 01N0 (equivalence of the two forms of the generation condition); Lemma 2.2
of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Pointwise value of a composite morphism on sections. -/
theorem comp_app_apply {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D) (U : X.Opens) (x : Γ(A, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

/-- A morphism of sheaves of modules commutes with restriction. -/
theorem app_map_res {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (x : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  _root_.PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

/-- Right whiskering on a pair of sections. -/
theorem whiskerRight_app_tensorSections {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

/-- `hom.app ∘ inv.app = id` for `Modules.tensor A B ≅ A ⊗ B`. -/
theorem tensorIsoTensorObj_hom_app_inv_app {A B : X.Modules} (U : X.Opens)
    (z : Γ(CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app U
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).inv.app U z) = z := by
  rw [← comp_app_apply, Iso.inv_hom_id, AlgebraicGeometry.Scheme.Modules.Hom.id_app]
  rfl

/-- Sections of a sheafification come locally from the presheaf: a section of `L P` over `U` is, near every point,
the image of a section under the sheafification unit `η`. Source: Mathlib's `Presheaf.isLocallySurjective_toSheafify`. -/
theorem exists_unit_app_eq_map (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : X.Opens)
    (s : Γ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P, U))
    (p : X) (hp : p ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧ ∃ t : P.obj (op V),
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
          (op V) t =
        ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).val.map
          (homOfLE hVU).op s := by
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf) s
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V, i, ⟨t, ht⟩, hpV⟩ := hmem p hp
  exact ⟨V, leOfHom i, hpV, t, ht⟩

/-- Restricting twice is restricting once. -/
theorem map_map_res {M : X.Modules} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- The pairing of sections commutes with restriction (`presheaf.map` spelling). -/
theorem tensorSections_map {A B : X.Modules} {U V : X.Opens} (h : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).presheaf.map (homOfLE h).op
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B V
        (A.presheaf.map (homOfLE h).op a) (B.presheaf.map (homOfLE h).op b) :=
  AlgebraicGeometry.Scheme.Modules.tensorSections_restrict A B (homOfLE h) a b

/-- Sections of `Modules.tensor A B` come locally from the presheaf of pure tensors: a special case of
`exists_unit_app_eq_map`. -/
theorem exists_tensor_unit_app_eq_map (A B : X.Modules) (U : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensor A B, U)) (p : X) (hp : p ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), p ∈ V ∧
      ∃ z : (CategoryTheory.MonoidalCategoryStruct.tensorObj
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)).obj (op V),
      ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (CategoryTheory.MonoidalCategoryStruct.tensorObj
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
          ((SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B))).app (op V) z =
        (AlgebraicGeometry.Scheme.Modules.tensor A B).presheaf.map (homOfLE hVU).op y :=
  exists_unit_app_eq_map _ U y p hp

end AlgebraicGeometry.Scheme.GradedQCAlgebra.GenAux

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The generating set `A(U)_0 ∪ A(U)_m`. -/
def genSet (U : X.Opens) (m : ℕ) : Set (S.sectionsRing U) :=
  (S.sectionsGrading U 0 : Set (S.sectionsRing U)) ∪ (S.sectionsGrading U m : Set (S.sectionsRing U))

/-- An element `ofPiece a` of the section ring lies in the corresponding graded piece. -/
theorem ofPiece_mem_sectionsGrading (U : X.Opens) (j : ℕ) (a : S.sectionsPiece U j) :
    S.ofPiece U j a ∈ S.sectionsGrading U j :=
  ⟨a, rfl⟩

theorem sectionsUnitHom_mem_closure (U : X.Opens) (m : ℕ) (r : Γ(X, U)) :
    S.sectionsUnitHom U r ∈ Subring.closure (S.genSet U m) :=
  Subring.subset_closure (Or.inl (S.sectionsUnit U r).2)

/-- Restriction sends `closure(A(V)_0 ∪ A(V)_m)` into `closure(A(U)_0 ∪ A(U)_m)`. -/
theorem sectionsRestrictHom_mem_closure {U V : X.Opens} (h : U ≤ V) (m : ℕ) {x : S.sectionsRing V}
    (hx : x ∈ Subring.closure (S.genSet V m)) :
    S.sectionsRestrictHom h x ∈ Subring.closure (S.genSet U m) := by
  have h1 := Subring.mem_closure_image_of (S.sectionsRestrictHom h) hx
  refine Subring.closure_mono ?_ h1
  rintro y ⟨z, hz, rfl⟩
  rcases hz with hz | hz
  · exact Or.inl ((S.sectionsRestrict h).map_mem hz)
  · exact Or.inr ((S.sectionsRestrict h).map_mem hz)

/-- The value of `mulPowOne (ℓ+1)` on "a section of the tensor power ⊗ a section of degree one": first compute
`mulPowOne ℓ`, then multiply. -/
theorem mulPowOne_succ_app' (T : X.GradedQCAlgebra) (ℓ : ℕ) (C : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow (T.part 1) ℓ, C)) (b : Γ(T.part 1, C)) :
    (T.mulPowOne (ℓ + 1)).app C
        ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (T.part 1) ℓ) (T.part 1)).inv.app C
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (AlgebraicGeometry.Scheme.Modules.tensorPow (T.part 1) ℓ) (T.part 1) C y b)) =
      (T.mul ℓ 1).app C (AlgebraicGeometry.Scheme.Modules.tensorSections (T.part ℓ) (T.part 1) C
        ((T.mulPowOne ℓ).app C y) b) := by
  show ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (T.part 1) ℓ) (T.part 1)).hom ≫
        (T.mulPowOne ℓ ▷ T.part 1) ≫ T.mul ℓ 1).app C _ = _
  rw [GenAux.comp_app_apply, GenAux.comp_app_apply]
  refine congrArg ((T.mul ℓ 1).app C) ?_
  refine (congrArg ((T.mulPowOne ℓ ▷ T.part 1).app C)
    (GenAux.tensorIsoTensorObj_hom_app_inv_app C _)).trans ?_
  exact GenAux.whiskerRight_app_tensorSections (T.mulPowOne ℓ) C y b

/-- The value of the Veronese multiplication `S^{(m)}_ℓ ⊗ S^{(m)}_1 → S^{(m)}_{ℓ+1}` on a pair of sections is their
product in the section ring. -/
theorem veronese_mul_app_ofPiece' (m ℓ : ℕ) (C : X.Opens)
    (x : S.sectionsPiece C (ℓ * m)) (b : S.sectionsPiece C (1 * m)) :
    S.ofPiece C ((ℓ + 1) * m) (((S.veronese m).mul ℓ 1).app C
        (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part (ℓ * m)) (S.part (1 * m)) C x b)) =
      S.ofPiece C (ℓ * m) x * S.ofPiece C (1 * m) b := by
  have h1 : ((S.veronese m).mul ℓ 1).app C
      (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part (ℓ * m)) (S.part (1 * m)) C x b) =
      (eqToHom (congrArg S.part (add_mul ℓ 1 m).symm)).app C (S.sectionsGMul C x b) :=
    GenAux.comp_app_apply (S.mul (ℓ * m) (1 * m))
      (eqToHom (congrArg S.part (add_mul ℓ 1 m).symm)) C _
  refine (congrArg (S.ofPiece C ((ℓ + 1) * m)) h1).trans ?_
  refine (DirectSum.of_eq_of_gradedMonoid_eq
    (S.mk_eqToHom_app C (add_mul ℓ 1 m).symm (S.sectionsGMul C x b))).trans ?_
  exact (DirectSum.of_mul_of (A := S.sectionsPiece C) x b).symm

/-- The Veronese unit `mulPowOne 0 = veroneseOne` evaluated at `r ∈ Γ(X, C)` is `sectionsUnitHom C r` in the section
ring. -/
theorem ofPiece_veronese_mulPowOne_zero_app (m : ℕ) (C : X.Opens) (r : Γ(X, C)) :
    S.ofPiece C (0 * m) (((S.veronese m).mulPowOne 0).app C r) = S.sectionsUnitHom C r := by
  have h0 : ((S.veronese m).mulPowOne 0).app C r =
      (eqToHom (congrArg S.part (zero_mul m).symm)).app C (S.one.app C r) :=
    GenAux.comp_app_apply S.one (eqToHom (congrArg S.part (zero_mul m).symm)) C r
  refine (congrArg (S.ofPiece C (0 * m)) h0).trans ?_
  exact DirectSum.of_eq_of_gradedMonoid_eq (S.mk_eqToHom_app C (zero_mul m).symm (S.one.app C r))

/-! ## The local closure predicate and the induction on `ℓ` -/

variable (m : ℕ)

/-- The `mulPowOne ℓ`-image of a section `y`, placed in the section ring, lies in `closure(A(W)_0 ∪ A(W)_m)`. -/
def InCl (ℓ : ℕ) (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)) : Prop :=
  S.ofPiece W (ℓ * m) (((S.veronese m).mulPowOne ℓ).app W y) ∈ Subring.closure (S.genSet W m)

/-- `InCl` holds near every point. -/
def Good (ℓ : ℕ) (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)) : Prop :=
  ∀ p ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W), p ∈ W' ∧
    S.InCl m ℓ W' ((AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ).presheaf.map
      (homOfLE h).op y)

variable {S} {m}

theorem InCl.restrict {ℓ : ℕ} {W : X.Opens}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)}
    (hy : S.InCl m ℓ W y) {W₀ : X.Opens} (h : W₀ ≤ W) :
    S.InCl m ℓ W₀ ((AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ).presheaf.map
      (homOfLE h).op y) := by
  unfold InCl at hy ⊢
  rw [GenAux.app_map_res]
  have e : S.ofPiece W₀ (ℓ * m)
      (((S.veronese m).part ℓ).presheaf.map (homOfLE h).op (((S.veronese m).mulPowOne ℓ).app W y))
      = S.sectionsRestrictHom h (S.ofPiece W (ℓ * m) (((S.veronese m).mulPowOne ℓ).app W y)) :=
    (S.sectionsRestrictHom_ofPiece h (ℓ * m) _).symm
  rw [e]
  exact S.sectionsRestrictHom_mem_closure h m hy

theorem InCl.zero (S : X.GradedQCAlgebra) (m ℓ : ℕ) (W : X.Opens) : S.InCl m ℓ W 0 := by
  unfold InCl
  refine Set.mem_of_eq_of_mem ?_ (Subring.zero_mem _)
  exact (congrArg (S.ofPiece W (ℓ * m))
    (map_zero (ConcreteCategory.hom (((S.veronese m).mulPowOne ℓ).app W)))).trans
    (map_zero (DirectSum.of (S.sectionsPiece W) (ℓ * m)))

theorem InCl.add {ℓ : ℕ} {W : X.Opens}
    {y₁ y₂ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)}
    (h₁ : S.InCl m ℓ W y₁) (h₂ : S.InCl m ℓ W y₂) : S.InCl m ℓ W (y₁ + y₂) := by
  unfold InCl at h₁ h₂ ⊢
  refine Set.mem_of_eq_of_mem ?_ (Subring.add_mem _ h₁ h₂)
  exact (congrArg (S.ofPiece W (ℓ * m))
    (map_add (ConcreteCategory.hom (((S.veronese m).mulPowOne ℓ).app W)) y₁ y₂)).trans
    (map_add (DirectSum.of (S.sectionsPiece W) (ℓ * m)) _ _)

theorem Good.of_inCl {ℓ : ℕ} {W : X.Opens}
    {y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)}
    (hy : S.InCl m ℓ W y) : S.Good m ℓ W y :=
  fun _ hp => ⟨W, le_rfl, hp, hy.restrict le_rfl⟩

theorem Good.zero (S : X.GradedQCAlgebra) (m ℓ : ℕ) (W : X.Opens) : S.Good m ℓ W 0 :=
  Good.of_inCl (InCl.zero S m ℓ W)

theorem Good.add {ℓ : ℕ} {W : X.Opens}
    {y₁ y₂ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)}
    (h₁ : S.Good m ℓ W y₁) (h₂ : S.Good m ℓ W y₂) : S.Good m ℓ W (y₁ + y₂) := by
  intro p hp
  obtain ⟨W₁, hW₁, hp₁, hIn₁⟩ := h₁ p hp
  obtain ⟨W₂, hW₂, hp₂, hIn₂⟩ := h₂ p hp
  refine ⟨W₁ ⊓ W₂, inf_le_left.trans hW₁, ⟨hp₁, hp₂⟩, ?_⟩
  rw [map_add]
  have e₁ := hIn₁.restrict (W₀ := W₁ ⊓ W₂) inf_le_left
  have e₂ := hIn₂.restrict (W₀ := W₁ ⊓ W₂) inf_le_right
  rw [GenAux.map_map_res] at e₁ e₂
  exact e₁.add e₂

/-- Pure tensors: if `a` satisfies `Good ℓ`, then `a ⊗ b` (put back into `tensorPow (ℓ+1)` via
`tensorIsoTensorObj.inv`) satisfies `Good (ℓ+1)`. -/
theorem Good.tmul {ℓ : ℕ} {W : X.Opens}
    {a : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)}
    (ha : S.Good m ℓ W a) (b : Γ((S.veronese m).part 1, W)) :
    S.Good m (ℓ + 1) W ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ)
        ((S.veronese m).part 1)).inv.app W
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ)
        ((S.veronese m).part 1) W a b)) := by
  intro p hp
  obtain ⟨W', hW', hpW', hIn⟩ := ha p hp
  refine ⟨W', hW', hpW', ?_⟩
  unfold InCl at hIn ⊢
  set a' := (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ).presheaf.map
    (homOfLE hW').op a with ha'
  set b' := ((S.veronese m).part 1).presheaf.map (homOfLE hW').op b with hb'
  have e0 := (GenAux.app_map_res (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ) ((S.veronese m).part 1)).inv
    hW' (AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ) ((S.veronese m).part 1) W a b)).symm
  rw [GenAux.tensorSections_map] at e0
  have e1 := congrArg (S.ofPiece W' ((ℓ + 1) * m)) ((S.veronese m).mulPowOne_succ_app' ℓ W' a' b')
  have e2 := S.veronese_mul_app_ofPiece' m ℓ W' (((S.veronese m).mulPowOne ℓ).app W' a') b'
  have hb : S.ofPiece W' (1 * m) b' ∈ S.sectionsGrading W' m := by
    have e : S.sectionsGrading W' (1 * m) = S.sectionsGrading W' m :=
      congrArg (S.sectionsGrading W') (Nat.one_mul m)
    exact e ▸ S.ofPiece_mem_sectionsGrading W' (1 * m) b'
  refine Set.mem_of_eq_of_mem (((congrArg (fun t => S.ofPiece W' ((ℓ + 1) * m)
    (((S.veronese m).mulPowOne (ℓ + 1)).app W' t)) e0).trans e1).trans e2) ?_
  exact Subring.mul_mem _ hIn (Subring.subset_closure (Or.inr hb))

/-- **Main induction**: every section of `tensorPow (S_m) ℓ` satisfies `Good ℓ`.
`ℓ = 0`: `mulPowOne 0 = veroneseOne`, whose image is `sectionsUnitHom`, lies in `A(W)_0`.
`ℓ + 1`: sections come locally from the presheaf tensor product (the sheafification unit is locally surjective); for
pure tensors use `Good.tmul` and the induction hypothesis, for sums `Good.add`. -/
theorem good_all (S : X.GradedQCAlgebra) (m ℓ : ℕ) : ∀ (W : X.Opens)
    (y : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ, W)),
    S.Good m ℓ W y := by
  induction ℓ with
  | zero =>
    intro W y
    apply Good.of_inCl
    unfold InCl
    rw [S.ofPiece_veronese_mulPowOne_zero_app m W y]
    exact S.sectionsUnitHom_mem_closure W m y
  | succ ℓ ih =>
    intro W y p hp
    obtain ⟨V, hVW, hpV, z, hz⟩ := GenAux.exists_tensor_unit_app_eq_map
      (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ) ((S.veronese m).part 1)
      W y p hp
    have key : ∀ z, S.Good m (ℓ + 1) V
        (((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
                (AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) ℓ))
            ((SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
                ((S.veronese m).part 1)))).app (op V) z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
        exact (congrArg (S.Good m (ℓ + 1) V) (map_zero _)).mpr (Good.zero S m (ℓ + 1) V)
      | tmul a b =>
        exact (congrArg (S.Good m (ℓ + 1) V)
          (AlgebraicGeometry.Scheme.Modules.tensorToSheafify_tensorSections _ _ V a b)).mp
          ((ih V a).tmul b)
      | add z₁ z₂ h₁ h₂ =>
        exact (congrArg (S.Good m (ℓ + 1) V) (map_add _ z₁ z₂)).mpr (h₁.add h₂)
    have hk := key z
    rw [hz] at hk
    have hk' : S.Good m (ℓ + 1) V
        ((AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) (ℓ + 1)).presheaf.map
          (homOfLE hVW).op y) := hk
    obtain ⟨W', hW', hpW', hIn⟩ := hk' p hpV
    refine ⟨W', hW'.trans hVW, hpW', ?_⟩
    rw [GenAux.map_map_res] at hIn
    exact hIn

/-! ## Localization: from `D(f)` back to the affine open `U` -/

variable (S)

/-- Lifting on a homogeneous piece: a section of the `j`-th piece over `D(f)`, multiplied by a power of `f`, comes from
`U` (`S.part j` is quasi-coherent). -/
theorem exists_pow_mul_eq_restrict_ofPiece {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (f : Γ(X, U)) (j : ℕ) (t : S.sectionsPiece (X.basicOpen f) j) :
    ∃ (n : ℕ) (t' : S.sectionsPiece U j),
      S.sectionsRestrictHom (X.basicOpen_le f) (S.ofPiece U j t') =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n *
          S.ofPiece (X.basicOpen f) j t := by
  have : (S.part j).IsQuasicoherent := S.quasicoherent j
  obtain ⟨n, t', ht'⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_map_basicOpen (S.part j) hU f t
  refine ⟨n, t', ?_⟩
  exact (S.sectionsRestrictHom_ofPiece (X.basicOpen_le f) j t').trans
    ((congrArg (S.ofPiece (X.basicOpen f) j) ht').trans
      ((S.sectionsUnitHom_mul_ofPiece (X.basicOpen f) _ t).symm.trans
        (congrArg (· * S.ofPiece (X.basicOpen f) j t)
          (map_pow (S.sectionsUnitHom (X.basicOpen f)) _ n))))

/-- **Lifting through localization**: an element of the closure over `D(f)`, multiplied by a power of `f`, comes from an
element of the closure over `U`. Proof: induction over `Subring.closure`; generators by
`exists_pow_mul_eq_restrict_ofPiece`, sums by adding the exponents. -/
theorem exists_pow_mul_eq_restrict_of_mem_closure {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    (f : Γ(X, U)) (m : ℕ) {z : S.sectionsRing (X.basicOpen f)}
    (hz : z ∈ Subring.closure (S.genSet (X.basicOpen f) m)) :
    ∃ (n : ℕ) (w : S.sectionsRing U), w ∈ Subring.closure (S.genSet U m) ∧
      S.sectionsRestrictHom (X.basicOpen_le f) w =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n * z := by
  have hres : S.sectionsRestrictHom (X.basicOpen_le f) (S.sectionsUnitHom U f) =
      S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) :=
    S.sectionsUnitHom_naturality (X.basicOpen_le f) f
  induction hz using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨n, t', ht'⟩ := S.exists_pow_mul_eq_restrict_ofPiece hU f 0 t
      exact ⟨n, S.ofPiece U 0 t',
        Subring.subset_closure (Or.inl (S.ofPiece_mem_sectionsGrading U 0 t')), ht'⟩
    · obtain ⟨n, t', ht'⟩ := S.exists_pow_mul_eq_restrict_ofPiece hU f m t
      exact ⟨n, S.ofPiece U m t',
        Subring.subset_closure (Or.inr (S.ofPiece_mem_sectionsGrading U m t')), ht'⟩
  | zero => exact ⟨0, 0, Subring.zero_mem _, by rw [map_zero, mul_zero]⟩
  | one => exact ⟨0, 1, Subring.one_mem _, by rw [map_one, pow_zero, _root_.one_mul]⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := ih₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := ih₂
    refine ⟨n₁ + n₂, S.sectionsUnitHom U f ^ n₂ * w₁ + S.sectionsUnitHom U f ^ n₁ * w₂, ?_, ?_⟩
    · exact Subring.add_mem _
        (Subring.mul_mem _ (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure U m f) _) hw₁)
        (Subring.mul_mem _ (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure U m f) _) hw₂)
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hres, e₁, e₂]
      ring
  | neg y _ ih =>
    obtain ⟨n, w, hw, e⟩ := ih
    exact ⟨n, -w, Subring.neg_mem _ hw, by rw [map_neg, e, mul_neg]⟩
  | mul y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := ih₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := ih₂
    refine ⟨n₁ + n₂, w₁ * w₂, Subring.mul_mem _ hw₁ hw₂, ?_⟩
    rw [map_mul, e₁, e₂, pow_add]
    ring

/-- **Kernel of the localization**: an element of the section ring whose restriction to `D(f)` vanishes is killed by a
power of `f` (`affineUnit_coequifibered`: `A(D f) = A(U)[1/f]`). -/
theorem exists_pow_mul_eq_zero_of_restrict_eq_zero (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens))
    (x : S.sectionsRing U.toOpens) (hx : S.sectionsRestrictHom (X.basicOpen_le f) x = 0) :
    ∃ n : ℕ, S.sectionsUnitHom U.toOpens f ^ n * x = 0 := by
  have h := S.affineUnit_coequifibered
  rw [AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway] at h
  have hloc := h U f
  let _ : Algebra (S.sectionsRing U.toOpens) (S.sectionsRing (X.basicOpen f)) :=
    (S.sectionsRestrictHom (X.basicOpen_le f)).toAlgebra
  have hloc' : IsLocalization.Away (S.sectionsUnitHom U.toOpens f) (S.sectionsRing (X.basicOpen f)) :=
    hloc
  have h0 : algebraMap (S.sectionsRing U.toOpens) (S.sectionsRing (X.basicOpen f)) x = 0 := hx
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
    (M := Submonoid.powers (S.sectionsUnitHom U.toOpens f)) (S := S.sectionsRing (X.basicOpen f)) x).mp h0
  exact ⟨n, hc⟩

/-! ## The main theorem -/

/-- Sufficient divisibility at the sheaf level (`GradedQCAlgebra.SufficientlyDivisible`: `m > 0` and the maps
`mulPowOne ℓ : (S_m)^{⊗ℓ} → S_{ℓm}` of the Veronese subalgebra `S^{(m)}` (`part ℓ := S.part (ℓ * m)`) are epimorphisms
for `ℓ > 0`) implies sufficient divisibility at the level of section rings (`GradedAffineAlgebra.SufficientlyDivisible`:
`m > 0` and for every affine open `U` and every `k`, `A(U)_{mk}` is contained in the subring generated by
`A(U)_0 ∪ A(U)_m`; note that `S.toGradedAffineAlgebra.grading U = S.sectionsGrading U` definitionally).
Sources: Stacks 01N0 (equivalence of the two forms of the generation condition) and localization of quasi-coherent
sheaves on principal opens (`affineUnit_coequifibered`), in the spirit of Stacks 01I8.
Proof (no `H^1`-vanishing of Stacks 01XB is used, only localization on principal opens):
1. For `k = 0`, `A(U)_0 ⊆ closure`. For `k > 0` write `a = ofPiece s` with `s ∈ Γ(U, S_{km})`. An epimorphism is locally
   surjective on sections (`epi_iff_locally_surjective_sections`): near every point `p`, `s|_V = mulPowOne k (y)`.
2. `good_all`: every section `y` of the tensor power satisfies, near every point, `ofPiece (mulPowOne k y) ∈ closure`
   — by induction on `k`; the sheafification unit is locally surjective (Mathlib's `isLocallySurjective_toSheafify`),
   so `y` is locally a sum of pure tensors, and `mulPowOne_succ_app'` and `veronese_mul_app_ofPiece'` send pure tensors
   to products.
3. Take a principal open `D(f) ∋ p` (`IsAffineOpen.exists_basicOpen_le`); then `ofPiece (s|_{D f}) ∈ closure(A(D f))`;
   lift with `exists_pow_mul_eq_restrict_of_mem_closure`: `f^n s` agrees on `D(f)` with some `w ∈ closure(A(U))`;
   `exists_pow_mul_eq_zero_of_restrict_eq_zero` (`A(D f) = A(U)[1/f]`): `f^N (w − f^n s) = 0`, hence
   `f^{N+n} a ∈ closure`.
4. `{r ∈ Γ(X,U) | r a ∈ closure}` is an ideal `I` containing some `f_p^{e_p}` (`e_p ≥ 1`) for every point `p`, so the
   `D(f_p^{e_p})` cover `U`; `U` is affine (`IsAffineOpen.self_le_iSup_basicOpen_iff`), hence `I = ⊤`, `1 ∈ I` and
   `a ∈ closure`.
The Veronese algebra has `part ℓ = S.part (ℓ * m)` while `GeneratedInDegree m` is written with `𝒜 (m * k)`; the two
agree by `Nat.mul_comm`, and the user `twistMul_isIso_of_dvd` applies this statement in the form
`hgen (affineSite U) k a ha` with `ha : a ∈ S.sectionsGrading U (m * k)`. -/
theorem _root_.AlgebraicGeometry.Scheme.GradedQCAlgebra.SufficientlyDivisible.toGradedAffineAlgebra
    {X : AlgebraicGeometry.Scheme.{u}} {S : X.GradedQCAlgebra} {m : ℕ} (hm : S.SufficientlyDivisible m) :
    S.toGradedAffineAlgebra.SufficientlyDivisible m := by
  refine ⟨hm.1, ?_⟩
  intro U k a ha
  change a ∈ S.sectionsGrading U.toOpens (m * k) at ha
  change a ∈ Subring.closure (S.genSet U.toOpens m)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.mul_zero] at ha
    exact Subring.subset_closure (Or.inl ha)
  rw [Nat.mul_comm] at ha
  obtain ⟨s, rfl⟩ := ha
  have hUaff : AlgebraicGeometry.IsAffineOpen U.toOpens := U.2
  have hepi := (AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections
    ((S.veronese m).mulPowOne k)).mp (hm.2 k hk)
  -- the ideal I = {r | r · a ∈ closure}
  let I : Ideal Γ(X, U.toOpens) :=
    { carrier := {r | S.sectionsUnitHom U.toOpens r * S.ofPiece U.toOpens (k * m) s ∈
        Subring.closure (S.genSet U.toOpens m)}
      zero_mem' := by
        rw [Set.mem_ofPred_eq, map_zero, zero_mul]
        exact Subring.zero_mem _
      add_mem' := by
        intro r₁ r₂ h₁ h₂
        rw [Set.mem_ofPred_eq] at h₁ h₂ ⊢
        rw [map_add, add_mul]
        exact Subring.add_mem _ h₁ h₂
      smul_mem' := by
        intro c r h
        rw [Set.mem_ofPred_eq] at h ⊢
        rw [smul_eq_mul, map_mul, _root_.mul_assoc]
        exact Subring.mul_mem _ (S.sectionsUnitHom_mem_closure U.toOpens m c) h }
  have hpt : ∀ p ∈ U.toOpens, ∃ g : Γ(X, U.toOpens), g ∈ I ∧ p ∈ X.basicOpen g := by
    intro p hp
    obtain ⟨V, hVU, hpV, y, hy⟩ := hepi U.toOpens s p hp
    obtain ⟨W', hW'V, hpW', hIn⟩ := S.good_all m k V y p hpV
    obtain ⟨f, hfW', hpf⟩ := hUaff.exists_basicOpen_le (V := W') ⟨p, hpW'⟩ hp
    have hV : X.basicOpen f ≤ U.toOpens := X.basicOpen_le f
    have hres : S.sectionsRestrictHom hV (S.sectionsUnitHom U.toOpens f) =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) :=
      S.sectionsUnitHom_naturality hV f
    have hIn2 := hIn.restrict (W₀ := X.basicOpen f) hfW'
    unfold InCl at hIn2
    rw [GenAux.map_map_res] at hIn2
    have hs : ((S.veronese m).mulPowOne k).app (X.basicOpen f)
        ((AlgebraicGeometry.Scheme.Modules.tensorPow ((S.veronese m).part 1) k).presheaf.map
          (homOfLE (hfW'.trans hW'V)).op y) =
        ((S.veronese m).part k).presheaf.map (homOfLE hV).op s :=
      (GenAux.app_map_res ((S.veronese m).mulPowOne k) (hfW'.trans hW'V) y).trans
        ((congrArg (fun t => ((S.veronese m).part k).presheaf.map (homOfLE (hfW'.trans hW'V)).op t) hy).trans
          (GenAux.map_map_res (M := (S.veronese m).part k) (hfW'.trans hW'V) hVU s))
    have hIn3 : S.ofPiece (X.basicOpen f) (k * m) (((S.veronese m).part k).presheaf.map (homOfLE hV).op s)
        ∈ Subring.closure (S.genSet (X.basicOpen f) m) :=
      Set.mem_of_eq_of_mem (congrArg (S.ofPiece (X.basicOpen f) (k * m)) hs).symm hIn2
    obtain ⟨n, w, hw, hwe⟩ := S.exists_pow_mul_eq_restrict_of_mem_closure hUaff f m hIn3
    have e4 : S.sectionsRestrictHom hV (S.sectionsUnitHom U.toOpens f ^ n * S.ofPiece U.toOpens (k * m) s) =
        S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) ^ n *
          S.ofPiece (X.basicOpen f) (k * m) (((S.veronese m).part k).presheaf.map (homOfLE hV).op s) := by
      rw [map_mul, map_pow, hres]
      exact congrArg (S.sectionsUnitHom (X.basicOpen f) (X.presheaf.map (homOfLE hV).op f) ^ n * ·)
        (S.sectionsRestrictHom_ofPiece hV (k * m) s)
    have e5 : S.sectionsRestrictHom hV
        (w - S.sectionsUnitHom U.toOpens f ^ n * S.ofPiece U.toOpens (k * m) s) = 0 := by
      rw [map_sub, hwe, e4, sub_self]
    obtain ⟨N, hN⟩ := S.exists_pow_mul_eq_zero_of_restrict_eq_zero U f _ e5
    have e6 : S.sectionsUnitHom U.toOpens f ^ N *
        (S.sectionsUnitHom U.toOpens f ^ n * S.ofPiece U.toOpens (k * m) s) =
        S.sectionsUnitHom U.toOpens f ^ N * w := by
      rw [mul_sub, sub_eq_zero] at hN
      exact hN.symm
    have hmem : S.sectionsUnitHom U.toOpens (f ^ (N + n)) * S.ofPiece U.toOpens (k * m) s ∈
        Subring.closure (S.genSet U.toOpens m) := by
      rw [map_pow, pow_add, _root_.mul_assoc, e6]
      exact Subring.mul_mem _ (Subring.pow_mem _ (S.sectionsUnitHom_mem_closure U.toOpens m f) N) hw
    refine ⟨f ^ (N + n + 1), ?_, ?_⟩
    · have : f ^ (N + n) ∈ I := hmem
      rw [pow_succ]
      exact I.mul_mem_right f this
    · rw [X.basicOpen_pow f (Nat.succ_pos _)]
      exact hpf
  have hcov : U.toOpens ≤ ⨆ g : (I : Set Γ(X, U.toOpens)), X.basicOpen g.1 := by
    intro p hp
    obtain ⟨g, hgI, hpg⟩ := hpt p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hgI⟩, hpg⟩
  have hspan : Ideal.span (I : Set Γ(X, U.toOpens)) = ⊤ := hUaff.self_le_iSup_basicOpen_iff.mp hcov
  rw [Ideal.span_eq] at hspan
  have h1 : (1 : Γ(X, U.toOpens)) ∈ I := hspan ▸ Submodule.mem_top
  have h1' : S.sectionsUnitHom U.toOpens 1 * S.ofPiece U.toOpens (k * m) s ∈
      Subring.closure (S.genSet U.toOpens m) := h1
  rw [map_one, _root_.one_mul] at h1'
  exact h1'

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
