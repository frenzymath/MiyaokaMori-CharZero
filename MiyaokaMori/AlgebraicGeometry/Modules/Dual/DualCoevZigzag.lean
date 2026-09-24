import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualEv
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.CategoryTheory.ZigzagBraided
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualEvSections
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection

/-! # The zigzag identities for coevaluation and evaluation

**The two zigzag identities for `(coev_V, ev_V)` on `X`.** For `V` locally free of finite type let
`coevHom V : O_X ⟶ V^∨ ⊗ V` be the morphism `1 ↦ coevSection V` (`homOfTopSection`, then
`Modules.tensor ≅ ⊗`) and `dualEv V : V^∨ ⊗ V ⟶ O_X` the evaluation. Then

* `zigzag1`: `(ρ_).inv ≫ V^∨ ◁ coev ≫ α⁻¹ ≫ β ▷ V ≫ α ≫ V^∨ ◁ ev ≫ ρ_ = 𝟙 V^∨`
  (elementwise `φ ↦ Σ_j ⟨φ, e_j⟩ e_j^∨ = φ`), and
* `zigzag2`: `(λ_).inv ≫ coev ▷ V ≫ α ≫ V^∨ ◁ β ≫ α⁻¹ ≫ ev ▷ V ≫ λ_ = 𝟙 V`
  (elementwise `v ↦ Σ_j ⟨e_j^∨, v⟩ e_j = v`),

in the form `Zigzag.Z1` / `Zigzag.Z2` of `ZigzagBraided`.

Proof. Both sides are morphisms of sheaves, so equality may be checked on sections over the opens `W ⊆ U_i`
of the trivializing cover `U_i = (locallyFreeData V).X i` (`hom_ext_of_cover_app`; for `zigzag1` first
reduce, by the sheafification adjunction, to sections of the form `dualUnit ψ`, `dual_hom_ext`, and then
localize with `section_ext_of_cover`). On such a `W`, `coevSection V|_W = coevLocal V i|_W`
(`coevSection_res`: the glued section restricts to the local pieces, `IsCompatible.section_apply`), and if
the frame `G_i` of `V|_{U_i}` is finite, `coevLocal V i|_W = Σ_j e_j^∨ ⊗ e_j` for the restricted frame
`(e, φ) = (resSec G_i.s, localDualRestrict (dualLocal G_i))` (`Frame.coevOfData_res`), which is a frame of
`V|_W` (`Frame.isFrameData_res`, `Frame.frameData`). The structural morphisms act on section pairs by
`associator_app_tensorSections`, `braiding_app_tensorSections`, `leftUnitor_app_tensorSections`,
`rightUnitor_app_tensorSections`, and evaluation by `dualEv_app_tensorSections_dualUnit`
(`DualEvSections`); the sums are pushed through by additivity. What remains is
`v = Σ_j φ_j(v) • e_j` (`IsFrameData.expand`) for `zigzag2` and `ψ = Σ_j ψ(e_j) • φ_j`
(`Frame.phi_eq_sum`) for `zigzag1`. If the frame `G_i` is infinite, `U_i = ⊥` because `V` is of finite type
(`Frame.finite_of_frames`), and sections over `⊥` form a subsingleton.

Source: Stacks 01CM/01CN (dual of a locally free module; `V^∨ ⊗ V ≅ 𝓗om(V, V)`, evaluation and
coevaluation). Used for the correspondence between sections and functionals on the total space of
a line bundle (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.DualZigzag

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### Elementary section-level helpers -/

theorem comp_app_apply' {A B E : X.Modules} (f : A ⟶ B) (g : B ⟶ E) (U : X.Opens) (x : Γ(A, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) := rfl

theorem iso_inv_app_hom_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens) (x : Γ(A, U)) :
    e.inv.app U (e.hom.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ U)
    e.hom_inv_id) x

theorem iso_inv_app_eq {A B : X.Modules} (e : A ≅ B) (U : X.Opens) {x : Γ(A, U)} {y : Γ(B, U)}
    (h : e.hom.app U x = y) : e.inv.app U y = x := by
  rw [← h]; exact iso_inv_app_hom_app e U x

theorem app_sum {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) {ι : Type*} (s : Finset ι)
    (x : ι → Γ(M, U)) : f.app U (∑ j ∈ s, x j) = ∑ j ∈ s, f.app U (x j) :=
  map_sum (f.app U).hom x s

theorem app_map_res' {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (x : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  _root_.PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

theorem whiskerRight_app_tensorSections' {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

theorem whiskerLeft_app_tensorSections' {A B B' : X.Modules} (f : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ f).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (f.app U b) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) f U a b

/-- The section `1 ∈ Γ(X, U)`, typed as a section of the monoidal unit `𝟙_ X.Modules` (so that `rw` can
match it in slots of type `Γ(𝟙_ X.Modules, U)`). -/
def unitOne (U : X.Opens) : Γ(𝟙_ X.Modules, U) := (1 : Γ(X, U))

theorem leftUnitor_inv_app (A : X.Modules) (U : X.Opens) (a : Γ(A, U)) :
    (λ_ A).inv.app U a =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A U (unitOne U) a :=
  iso_inv_app_eq _ _ ((AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections A U 1 a).trans
    (one_smul _ a))

theorem rightUnitor_inv_app (A : X.Modules) (U : X.Opens) (a : Γ(A, U)) :
    (ρ_ A).inv.app U a =
      AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a (unitOne U) :=
  iso_inv_app_eq _ _ ((AlgebraicGeometry.Scheme.Modules.rightUnitor_app_tensorSections A U a 1).trans
    (one_smul _ a))

theorem associator_inv_app_tensorSections (A B E : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (e : Γ(E, U)) :
    (α_ A B E).inv.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) B E) U a
        (AlgebraicGeometry.Scheme.Modules.tensorSections B E U b e)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B) E U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) e :=
  iso_inv_app_eq _ _ (AlgebraicGeometry.Scheme.Modules.associator_app_tensorSections A B E U a b e)

theorem tensorSections_sum_left (A B : X.Modules) (U : X.Opens) {ι : Type*} (s : Finset ι)
    (a : ι → Γ(A, U)) (b : Γ(B, U)) :
    AlgebraicGeometry.Scheme.Modules.tensorSections A B U (∑ j ∈ s, a j) b =
      ∑ j ∈ s, AlgebraicGeometry.Scheme.Modules.tensorSections A B U (a j) b :=
  map_sum (AddMonoidHom.mk' (fun a => AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b)
    (fun x y => AlgebraicGeometry.Scheme.Modules.tensorSections_add_left A B U x y b)) a s

theorem tensorSections_sum_right (A B : X.Modules) (U : X.Opens) {ι : Type*} (s : Finset ι)
    (a : Γ(A, U)) (b : ι → Γ(B, U)) :
    AlgebraicGeometry.Scheme.Modules.tensorSections A B U a (∑ j ∈ s, b j) =
      ∑ j ∈ s, AlgebraicGeometry.Scheme.Modules.tensorSections A B U a (b j) :=
  map_sum (AddMonoidHom.mk' (fun b => AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b)
    (fun x y => AlgebraicGeometry.Scheme.Modules.tensorSections_add_right A B U a x y)) b s

/-- `(unitHomEquiv M).symm σ` sends `1` to the component of `σ`. -/
theorem unitHomEquiv_symm_app_one (M : X.Modules) (σ : M.sections) (W : X.Opens) :
    AlgebraicGeometry.Scheme.Modules.Hom.app ((SheafOfModules.unitHomEquiv M).symm σ) W (unitOne W) =
      σ.val (op W) := by
  have h := congrArg (fun z : M.sections => z.val (op W))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply σ)
  exact h

/-- `homOfTopSection M s` sends `1 ∈ Γ(X, W)` to `s|_W`. -/
theorem homOfTopSection_app_one (M : X.Modules) (s : Γ(M, ⊤)) (W : X.Opens) :
    AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.homOfTopSection M s) W
        (unitOne W) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s :=
  unitHomEquiv_symm_app_one M _ W

/-! ### Locality -/

/-- Sections of a sheaf agreeing on the pieces `W ⊓ U i` of an open cover are equal. -/
theorem section_ext_of_cover {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (N : X.Modules)
    (W : X.Opens) (a b : Γ(N, W))
    (h : ∀ i, N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op a =
      N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op b) : a = b := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i => W ⊓ U i) W
    (fun i => homOfLE inf_le_left) ?_ a b h
  intro x hx
  have hx' : x ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- Two morphisms of sheaves of modules agreeing on all sections over opens contained in a member of an
open cover are equal. -/
theorem hom_ext_of_cover_app {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) {M N : X.Modules}
    (f g : M ⟶ N)
    (h : ∀ i (W : X.Opens), W ≤ U i → ∀ x : Γ(M, W), f.app W x = g.app W x) : f = g := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext f g fun W => ?_
  ext x
  refine section_ext_of_cover U hU N W _ _ fun i => ?_
  rw [← app_map_res', ← app_map_res']
  exact h i (W ⊓ U i) inf_le_right _

/-- Two morphisms agree on a section `x` over `W` if they agree on its restrictions to the pieces `W ⊓ U i`. -/
theorem app_eq_of_cover {ι : Type*} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) {M N : X.Modules}
    (f g : M ⟶ N) (W : X.Opens) (x : Γ(M, W))
    (h : ∀ i, f.app (W ⊓ U i) (M.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x) =
      g.app (W ⊓ U i) (M.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x)) :
    f.app W x = g.app W x := by
  refine section_ext_of_cover U hU N W _ _ fun i => ?_
  rw [← app_map_res', ← app_map_res']
  exact h i

/-- A morphism out of `dual V = L(moduleDualPresheaf V)` is determined by its values on the images
`dualUnit ψ` of the sheafification unit. -/
theorem sheafify_hom_ext (P : X.PresheafOfModules) {N : SheafOfModules.{u} X.ringCatSheaf}
    (f g : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P ⟶ N)
    (h : ∀ (W : X.Opens) (χ : P.obj (op W)),
      f.val.app (op W) (((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op W) χ) =
        g.val.app (op W) (((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app P).app (op W) χ)) : f = g := by
  apply ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv P N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext W χ
  exact h W.unop χ

theorem dual_hom_ext (V : X.Modules) {N : X.Modules} (f g : AlgebraicGeometry.Scheme.Modules.dual V ⟶ N)
    (h : ∀ (W : X.Opens) (ψ : AlgebraicGeometry.Scheme.Modules.Frame.LH V W),
      f.app W (AlgebraicGeometry.Scheme.Modules.Frame.dualUnit V W ψ) =
        g.app W (AlgebraicGeometry.Scheme.Modules.Frame.dualUnit V W ψ)) : f = g :=
  sheafify_hom_ext (AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf V) f g fun W ψ => h W ψ

/-! ### The coevaluation morphism and its restrictions -/

/-- The coevaluation as a morphism `O_X ⟶ V^∨ ⊗ V` (`1 ↦ coevSection V`). -/
def coevHom (V : X.Modules) [V.IsLocallyFree] :
    𝟙_ X.Modules ⟶ CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
      (AlgebraicGeometry.Scheme.Modules.dual V) V :=
  AlgebraicGeometry.Scheme.Modules.homOfTopSection _ (AlgebraicGeometry.Scheme.Modules.coevSection V) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V).hom

theorem coevHom_app_one (V : X.Modules) [V.IsLocallyFree] (W : X.Opens) :
    (coevHom V).app W (unitOne W) =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual V) V).hom.app
        W ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V).presheaf.map
          (homOfLE (le_top : W ≤ ⊤)).op (AlgebraicGeometry.Scheme.Modules.coevSection V)) :=
  congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (AlgebraicGeometry.Scheme.Modules.dual V) V).hom.app W z)
    (homOfTopSection_app_one (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V)
      (AlgebraicGeometry.Scheme.Modules.coevSection V) W)

/-- The glued section `coevSection V` restricts on `W ⊆ U_i` to the local piece `coevLocal V i`. -/
theorem coevSection_res (V : X.Modules) [V.IsLocallyFree]
    (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).I) (W : X.Opens)
    (hW : W ≤ (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i) :
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op (AlgebraicGeometry.Scheme.Modules.coevSection V) =
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V).presheaf.map
        (homOfLE hW).op (AlgebraicGeometry.Scheme.Modules.coevLocal V i) := by
  have hF : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat) :=
    (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)).mp
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual V) V).isSheaf
  let s := (AlgebraicGeometry.Scheme.Modules.coevLocal_isCompatible V).section_
    (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).coversTop hF
  have e0 : AlgebraicGeometry.Scheme.Modules.coevSection V = s.1 (op ⊤) := rfl
  have e1 : s.1 (op ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i)) =
      AlgebraicGeometry.Scheme.Modules.coevLocal V i :=
    (AlgebraicGeometry.Scheme.Modules.coevLocal_isCompatible V).section_apply
      (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).coversTop hF i
  have e2 := s.2 (homOfLE (le_top : W ≤ ⊤)).op
  have e3 := s.2 (homOfLE hW).op
  rw [e0, ← e1]
  exact e2.trans e3.symm

/-- If `V` is of finite type, an infinite frame of `locallyFreeData V` lives over the empty open. -/
theorem locallyFreeData_X_eq_bot_of_not_finite (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).I)
    (h : ¬ Finite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).generators i).I) :
    (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i = ⊥ := by
  by_contra hne
  obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u, u} (M := V)
  have hcov := σ.coversTop
  rw [_root_.Opens.coversTop_iff] at hcov
  have hz' : z ∈ (⨆ k, σ.X k : X.Opens) := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz'
  have := hσ.isFiniteType k
  haveI := (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData V).isIso i
  exact h (AlgebraicGeometry.Scheme.Modules.Frame.finite_of_frames V
    (homOfLE (inf_le_left : σ.X k ⊓ (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i ≤ σ.X k))
    (homOfLE inf_le_right) (σ.generators k)
    ((AlgebraicGeometry.Scheme.Modules.locallyFreeData V).generators i) z ⟨hk, hz⟩)

theorem locallyFreeData_iSup_eq_top (V : X.Modules) [V.IsLocallyFree] :
    (⨆ i, (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).X i : X.Opens) = ⊤ := by
  have hcov := (AlgebraicGeometry.Scheme.Modules.locallyFreeData V).coversTop
  rw [_root_.Opens.coversTop_iff] at hcov
  exact hcov

/-! ### The local computation -/

section Local

variable (V : X.Modules) [V.IsLocallyFree]

open AlgebraicGeometry.Scheme.Modules.Frame in
/-- On `W ⊆ U_i` with `U_i` carrying a finite frame, `coevSection V|_W` is `Σ_j e_j^∨ ⊗ e_j` for the
restricted frame (`dualBasisLocalHom V i j = dualLocal` of the `i`-th frame). -/
theorem coevHom_app_one_eq_sum (i : (locallyFreeData V).I) [hfin : Finite ((locallyFreeData V).generators i).I]
    (W : X.Opens) (hW : W ≤ (locallyFreeData V).X i) :
    letI := Fintype.ofFinite ((locallyFreeData V).generators i).I
    (coevHom V).app W (unitOne W) =
      ∑ j, tensorSections (dual V) V W
        (dualUnit V W (AlgebraicGeometry.Scheme.Modules.localDualRestrict V (homOfLE hW) (dualBasisLocalHom V i j)))
        (secTop V W (resSec V (homOfLE hW) (((locallyFreeData V).generators i).s j))) := by
  letI := Fintype.ofFinite ((locallyFreeData V).generators i).I
  rw [coevHom_app_one, coevSection_res V i W hW]
  unfold AlgebraicGeometry.Scheme.Modules.coevLocal
  rw [dif_pos hfin, coevOfData_res]
  unfold coevOfData
  exact (app_sum _ _ _ _).trans (Finset.sum_congr rfl fun j _ => rfl)

/-- The tail `α ≫ V^∨ ◁ β ≫ α⁻¹ ≫ ev ▷ V ≫ λ` of the second zigzag composite. -/
def tail2 : (dual V ⊗ V) ⊗ V ⟶ V :=
  (α_ (dual V) V V).hom ≫ dual V ◁ (β_ V V).hom ≫ (α_ (dual V) V V).inv ≫ dualEv V ▷ V ≫ (λ_ V).hom

/-- The tail `α⁻¹ ≫ β ▷ V ≫ α ≫ V^∨ ◁ ev ≫ ρ` of the first zigzag composite. -/
def tail1 : dual V ⊗ (dual V ⊗ V) ⟶ dual V :=
  (α_ (dual V) (dual V) V).inv ≫ (β_ (dual V) (dual V)).hom ▷ V ≫ (α_ (dual V) (dual V) V).hom ≫
    dual V ◁ dualEv V ≫ (ρ_ (dual V)).hom

omit [V.IsLocallyFree] in
open AlgebraicGeometry.Scheme.Modules.Frame in
/-- `tail2` on a section triple `(φ ⊗ b) ⊗ v`: `φ(v) • b`. -/
theorem tail2_app (W : X.Opens) (ψ : LH V W) (b v : Γ(V, W)) :
    (tail2 V).app W (tensorSections (dual V ⊗ V) V W (tensorSections (dual V) V W (dualUnit V W ψ) b) v) =
      @HSMul.hSMul Γ(X, W) Γ(V, W) Γ(V, W) instHSMul (ψ.1 (topZ W) v) b := by
  have s1 := associator_app_tensorSections (dual V) V V W (dualUnit V W ψ) b v
  have s2 := (whiskerLeft_app_tensorSections' (A := dual V) (β_ V V).hom W (dualUnit V W ψ)
    (tensorSections V V W b v)).trans
    (congrArg (fun z => tensorSections (dual V) (V ⊗ V) W (dualUnit V W ψ) z)
      (braiding_app_tensorSections V V W b v))
  have s3 := associator_inv_app_tensorSections (dual V) V V W (dualUnit V W ψ) v b
  have s4 := (whiskerRight_app_tensorSections' (B := V) (dualEv V) W
    (tensorSections (dual V) V W (dualUnit V W ψ) v) b).trans
    (congrArg (fun z => tensorSections (SheafOfModules.unit X.ringCatSheaf) V W z b)
      (dualEv_app_tensorSections_dualUnit V W ψ v))
  have s5 : (λ_ V).hom.app W (tensorSections (SheafOfModules.unit X.ringCatSheaf) V W (ψ.1 (topZ W) v) b) =
      @HSMul.hSMul Γ(X, W) Γ(V, W) Γ(V, W) instHSMul (ψ.1 (topZ W) v) b :=
    leftUnitor_app_tensorSections V W _ _
  show (λ_ V).hom.app W ((dualEv V ▷ V).app W ((α_ (dual V) V V).inv.app W ((dual V ◁ (β_ V V).hom).app W
    ((α_ (dual V) V V).hom.app W
      (tensorSections (dual V ⊗ V) V W (tensorSections (dual V) V W (dualUnit V W ψ) b) v))))) = _
  rw [s1, s2, s3, s4, s5]

omit [V.IsLocallyFree] in
open AlgebraicGeometry.Scheme.Modules.Frame in
/-- `tail1` on a section triple `ψ ⊗ (φ ⊗ b)`: `ψ(b) • φ`. -/
theorem tail1_app (W : X.Opens) (ψ ψ' : LH V W) (b : Γ(V, W)) :
    (tail1 V).app W (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
        (tensorSections (dual V) V W (dualUnit V W ψ') b)) =
      @HSMul.hSMul Γ(X, W) Γ(dual V, W) Γ(dual V, W) instHSMul (ψ.1 (topZ W) b) (dualUnit V W ψ') := by
  have s1 := associator_inv_app_tensorSections (dual V) (dual V) V W (dualUnit V W ψ) (dualUnit V W ψ') b
  have s2 := (whiskerRight_app_tensorSections' (B := V) (β_ (dual V) (dual V)).hom W
    (tensorSections (dual V) (dual V) W (dualUnit V W ψ) (dualUnit V W ψ')) b).trans
    (congrArg (fun z => tensorSections (dual V ⊗ dual V) V W z b)
      (braiding_app_tensorSections (dual V) (dual V) W (dualUnit V W ψ) (dualUnit V W ψ')))
  have s3 := associator_app_tensorSections (dual V) (dual V) V W (dualUnit V W ψ') (dualUnit V W ψ) b
  have s4 := (whiskerLeft_app_tensorSections' (A := dual V) (dualEv V) W (dualUnit V W ψ')
    (tensorSections (dual V) V W (dualUnit V W ψ) b)).trans
    (congrArg (fun z => tensorSections (dual V) (SheafOfModules.unit X.ringCatSheaf) W (dualUnit V W ψ') z)
      (dualEv_app_tensorSections_dualUnit V W ψ b))
  have s5 : (ρ_ (dual V)).hom.app W
      (tensorSections (dual V) (SheafOfModules.unit X.ringCatSheaf) W (dualUnit V W ψ') (ψ.1 (topZ W) b)) =
      @HSMul.hSMul Γ(X, W) Γ(dual V, W) Γ(dual V, W) instHSMul (ψ.1 (topZ W) b) (dualUnit V W ψ') :=
    rightUnitor_app_tensorSections (dual V) W _ _
  show (ρ_ (dual V)).hom.app W ((dual V ◁ dualEv V).app W ((α_ (dual V) (dual V) V).hom.app W
    (((β_ (dual V) (dual V)).hom ▷ V).app W ((α_ (dual V) (dual V) V).inv.app W
      (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
        (tensorSections (dual V) V W (dualUnit V W ψ') b)))))) = _
  rw [s1, s2, s3, s4, s5]

open AlgebraicGeometry.Scheme.Modules.Frame in
/-- The second zigzag identity on sections over `W`, given a finite frame `(e, φ)` of `V|_W` such that
`coev|_W = Σ_j φ_j ⊗ e_j`: `v ↦ Σ_j φ_j(v) e_j = v`. -/
theorem zigzag2_of_frame (W : X.Opens) {I : Type u} [Fintype I] (e : I → (V.over W).sections)
    (φ : I → LH V W) (hfr : IsFrameData V W e φ)
    (hc : (coevHom V).app W (unitOne W) =
      ∑ j, tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)))
    (v : Γ(V, W)) :
    ((λ_ V).inv ≫ coevHom V ▷ V ≫ tail2 V).app W v = v :=
  calc ((λ_ V).inv ≫ coevHom V ▷ V ≫ tail2 V).app W v
      = (tail2 V).app W ((coevHom V ▷ V).app W ((λ_ V).inv.app W v)) :=
        (comp_app_apply' (λ_ V).inv (coevHom V ▷ V ≫ tail2 V) W v).trans
          (comp_app_apply' (coevHom V ▷ V) (tail2 V) W _)
    _ = (tail2 V).app W ((coevHom V ▷ V).app W (tensorSections (𝟙_ X.Modules) V W (unitOne W) v)) :=
        congrArg (fun z => (tail2 V).app W ((coevHom V ▷ V).app W z)) (leftUnitor_inv_app V W v)
    _ = (tail2 V).app W (tensorSections (dual V ⊗ V) V W ((coevHom V).app W (unitOne W)) v) :=
        congrArg (fun z => (tail2 V).app W z) (whiskerRight_app_tensorSections' (coevHom V) W (unitOne W) v)
    _ = (tail2 V).app W (tensorSections (dual V ⊗ V) V W
          (∑ j, tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))) v) :=
        congrArg (fun z => (tail2 V).app W (tensorSections (dual V ⊗ V) V W z v)) hc
    _ = (tail2 V).app W (∑ j, tensorSections (dual V ⊗ V) V W
          (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))) v) :=
        congrArg (fun z => (tail2 V).app W z) (tensorSections_sum_left (dual V ⊗ V) V W Finset.univ
          (fun j => tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))) v)
    _ = ∑ j, (tail2 V).app W (tensorSections (dual V ⊗ V) V W
          (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))) v) :=
        app_sum (tail2 V) W Finset.univ
          (fun j => tensorSections (dual V ⊗ V) V W
            (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))) v)
    _ = ∑ j, @HSMul.hSMul Γ(X, W) Γ(V, W) Γ(V, W) instHSMul ((φ j).1 (topZ W) v) (secTop V W (e j)) :=
        Finset.sum_congr rfl fun j _ => tail2_app V W (φ j) (secTop V W (e j)) v
    _ = v := (hfr.expand (topZ W) v).symm

open AlgebraicGeometry.Scheme.Modules.Frame in
/-- The first zigzag identity on the section `dualUnit ψ` over `W`, given a finite frame `(e, φ)` of `V|_W`
such that `coev|_W = Σ_j φ_j ⊗ e_j`: `ψ ↦ Σ_j ψ(e_j) φ_j = ψ`. -/
theorem zigzag1_of_frame (W : X.Opens) {I : Type u} [Fintype I] (e : I → (V.over W).sections)
    (φ : I → LH V W) (hfr : IsFrameData V W e φ)
    (hc : (coevHom V).app W (unitOne W) =
      ∑ j, tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)))
    (ψ : LH V W) :
    ((ρ_ (dual V)).inv ≫ dual V ◁ coevHom V ≫ tail1 V).app W (dualUnit V W ψ) = dualUnit V W ψ := by
  have hψ : ψ = ∑ k, @HSMul.hSMul Γ(X, W) (LH V W) (LH V W) instHSMul (ψ.1 (topZ W) (secTop V W (e k))) (φ k) :=
    phi_eq_sum V W (fun _ : PUnit.{u+1} => ψ) e φ hfr PUnit.unit
  calc ((ρ_ (dual V)).inv ≫ dual V ◁ coevHom V ≫ tail1 V).app W (dualUnit V W ψ)
      = (tail1 V).app W ((dual V ◁ coevHom V).app W ((ρ_ (dual V)).inv.app W (dualUnit V W ψ))) :=
        (comp_app_apply' (ρ_ (dual V)).inv (dual V ◁ coevHom V ≫ tail1 V) W _).trans
          (comp_app_apply' (dual V ◁ coevHom V) (tail1 V) W _)
    _ = (tail1 V).app W ((dual V ◁ coevHom V).app W
          (tensorSections (dual V) (𝟙_ X.Modules) W (dualUnit V W ψ) (unitOne W))) :=
        congrArg (fun z => (tail1 V).app W ((dual V ◁ coevHom V).app W z))
          (rightUnitor_inv_app (dual V) W (dualUnit V W ψ))
    _ = (tail1 V).app W (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ) ((coevHom V).app W (unitOne W))) :=
        congrArg (fun z => (tail1 V).app W z)
          (whiskerLeft_app_tensorSections' (coevHom V) W (dualUnit V W ψ) (unitOne W))
    _ = (tail1 V).app W (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
          (∑ j, tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)))) :=
        congrArg (fun z => (tail1 V).app W (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ) z)) hc
    _ = (tail1 V).app W (∑ j, tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
          (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)))) :=
        congrArg (fun z => (tail1 V).app W z) (tensorSections_sum_right (dual V) (dual V ⊗ V) W Finset.univ
          (dualUnit V W ψ) (fun j => tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))))
    _ = ∑ j, (tail1 V).app W (tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
          (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j)))) :=
        app_sum (tail1 V) W Finset.univ
          (fun j => tensorSections (dual V) (dual V ⊗ V) W (dualUnit V W ψ)
            (tensorSections (dual V) V W (dualUnit V W (φ j)) (secTop V W (e j))))
    _ = ∑ j, @HSMul.hSMul Γ(X, W) Γ(dual V, W) Γ(dual V, W) instHSMul (ψ.1 (topZ W) (secTop V W (e j)))
          (dualUnit V W (φ j)) :=
        Finset.sum_congr rfl fun j _ => tail1_app V W ψ (φ j) (secTop V W (e j))
    _ = dualUnit V W (∑ j, @HSMul.hSMul Γ(X, W) (LH V W) (LH V W) instHSMul (ψ.1 (topZ W) (secTop V W (e j)))
          (φ j)) := by
        rw [dualUnit_sum]; simp only [dualUnit_smul]
    _ = dualUnit V W ψ := by rw [← hψ]

open AlgebraicGeometry.Scheme.Modules.Frame in
/-- The second zigzag identity on sections over `W ⊆ U_i`. -/
theorem zigzag2_local [V.IsFiniteType] (i : (locallyFreeData V).I) (W : X.Opens)
    (hW : W ≤ (locallyFreeData V).X i) (v : Γ(V, W)) :
    ((λ_ V).inv ≫ coevHom V ▷ V ≫ tail2 V).app W v = v := by
  by_cases hfin : Finite ((locallyFreeData V).generators i).I
  · let _ := Fintype.ofFinite ((locallyFreeData V).generators i).I
    have := (locallyFreeData_isLocallyFreeData V).isIso i
    exact zigzag2_of_frame V W _ _
      (isFrameData_res V (homOfLE hW) ((locallyFreeData V).generators i).s
        (dualLocal V ((locallyFreeData V).generators i)) (frameData V ((locallyFreeData V).generators i)))
      (coevHom_app_one_eq_sum V i W hW) v
  · have hbot := locallyFreeData_X_eq_bot_of_not_finite V i hfin
    have hW' : W = ⊥ := le_bot_iff.mp (hbot ▸ hW)
    subst hW'
    have := subsingleton_sections_bot V
    exact Subsingleton.elim _ _

open AlgebraicGeometry.Scheme.Modules.Frame in
/-- The first zigzag identity on sections `dualUnit ψ` over `W ⊆ U_i`. -/
theorem zigzag1_local [V.IsFiniteType] (i : (locallyFreeData V).I) (W : X.Opens)
    (hW : W ≤ (locallyFreeData V).X i) (ψ : LH V W) :
    ((ρ_ (dual V)).inv ≫ dual V ◁ coevHom V ≫ tail1 V).app W (dualUnit V W ψ) = dualUnit V W ψ := by
  by_cases hfin : Finite ((locallyFreeData V).generators i).I
  · let _ := Fintype.ofFinite ((locallyFreeData V).generators i).I
    have := (locallyFreeData_isLocallyFreeData V).isIso i
    exact zigzag1_of_frame V W _ _
      (isFrameData_res V (homOfLE hW) ((locallyFreeData V).generators i).s
        (dualLocal V ((locallyFreeData V).generators i)) (frameData V ((locallyFreeData V).generators i)))
      (coevHom_app_one_eq_sum V i W hW) ψ
  · have hbot := locallyFreeData_X_eq_bot_of_not_finite V i hfin
    have hW' : W = ⊥ := le_bot_iff.mp (hbot ▸ hW)
    subst hW'
    have := subsingleton_sections_bot (dual V)
    exact Subsingleton.elim _ _

/-- **Second zigzag identity on `X`** (`Zigzag.Z2`):
`(λ_).inv ≫ coev ▷ V ≫ α ≫ V^∨ ◁ β ≫ α⁻¹ ≫ ev ▷ V ≫ λ_ = 𝟙 V`. -/
theorem zigzag2 [V.IsFiniteType] : CategoryTheory.MonoidalCategory.Zigzag.Z2 (coevHom V) (dualEv V) := by
  unfold CategoryTheory.MonoidalCategory.Zigzag.Z2
  refine hom_ext_of_cover_app _ (locallyFreeData_iSup_eq_top V) _ _ fun i W hW v => ?_
  exact zigzag2_local V i W hW v

/-- **First zigzag identity on `X`** (`Zigzag.Z1`):
`(ρ_).inv ≫ V^∨ ◁ coev ≫ α⁻¹ ≫ β ▷ V ≫ α ≫ V^∨ ◁ ev ≫ ρ_ = 𝟙 V^∨`. -/
theorem zigzag1 [V.IsFiniteType] : CategoryTheory.MonoidalCategory.Zigzag.Z1 (coevHom V) (dualEv V) := by
  unfold CategoryTheory.MonoidalCategory.Zigzag.Z1
  refine dual_hom_ext V _ _ fun W ψ => ?_
  refine app_eq_of_cover _ (locallyFreeData_iSup_eq_top V) _ _ W _ fun i => ?_
  have hres := Frame.dualUnit_res V (homOfLE (inf_le_left : W ⊓ (locallyFreeData V).X i ≤ W)) ψ
  rw [hres]
  exact zigzag1_local V i _ inf_le_right _

end Local

end AlgebraicGeometry.Scheme.Modules.DualZigzag

end
