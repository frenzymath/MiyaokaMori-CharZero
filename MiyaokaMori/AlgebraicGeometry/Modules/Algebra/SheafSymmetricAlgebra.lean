import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesInternalHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom

/-! # The symmetric algebra of a sheaf of modules

The symmetric algebra `Sym(V)` of a sheaf of modules, as a graded quasi-coherent `O_X`-algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory ZeroObject

/-- The monoidal tensor power `V^{⊗n}` (in the monoidal structure of `X.Modules`, right-multiplication
recursion: `V^{⊗0} = 𝟙_`, `V^{⊗(n+1)} = V^{⊗n} ⊗ V`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.monoidalPow {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => AlgebraicGeometry.Scheme.Modules.monoidalPow V n ⊗ V

/-- Adjacent transpositions: `transp n i` swaps the `(i+1)`-st and `(i+2)`-nd factors of `V^{⊗n}` counted from
the right (for `i = 0` the braiding `β_` swaps the last two factors; otherwise recurse to the left and whisker
on the right by `V`); out of range it is the identity. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.monoidalPowTransp {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : (n : ℕ) → ℕ →
      (AlgebraicGeometry.Scheme.Modules.monoidalPow V n ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow V n)
  | n + 2, 0 =>
    (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow V n) V V).hom ≫
      (AlgebraicGeometry.Scheme.Modules.monoidalPow V n ◁ (β_ V V).hom) ≫
      (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow V n) V V).inv
  | n + 1, i + 1 => AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V n i ▷ V
  | _, _ => 𝟙 _

/-- The concatenation isomorphism `V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗(m+n)}` (recursion on `n`: right unitor and
associator). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.monoidalPowCat {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m : ℕ) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.monoidalPow V m ⊗ AlgebraicGeometry.Scheme.Modules.monoidalPow V n ≅
      AlgebraicGeometry.Scheme.Modules.monoidalPow V (m + n))
  | 0 => ρ_ (AlgebraicGeometry.Scheme.Modules.monoidalPow V m)
  | n + 1 =>
    (α_ (AlgebraicGeometry.Scheme.Modules.monoidalPow V m)
        (AlgebraicGeometry.Scheme.Modules.monoidalPow V n) V).symm ≪≫
      CategoryTheory.MonoidalCategory.whiskerRightIso
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat V m n) V

/-- The symmetric power `Sym^m V`: the coinvariants of `V^{⊗m}` under all adjacent transpositions (which
generate `S_m`), i.e. the wide coequalizer of the identity and the `transp m i` (`i < m`) (`X.Modules` has
colimits). For `m = 0` it is `𝟙_ = O_X`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPow {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m : ℕ) : X.Modules :=
  CategoryTheory.Limits.wideCoequalizer
    (fun j : ULift.{u} (Option (Fin m)) =>
      match j.down with
      | none => 𝟙 (AlgebraicGeometry.Scheme.Modules.monoidalPow V m)
      | some i => AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V m i)

/-- The quotient map `V^{⊗m} → Sym^m V`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPowπ {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPow V m ⟶ AlgebraicGeometry.Scheme.Modules.symPow V m :=
  CategoryTheory.Limits.wideCoequalizer.π _

/-- Descent along the quotient map: a morphism `V^{⊗m} → W` invariant under every adjacent transposition gives
`Sym^m V → W` (the invariance is a hypothesis). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPowDesc {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m : ℕ) {W : X.Modules}
    (k : AlgebraicGeometry.Scheme.Modules.monoidalPow V m ⟶ W)
    (hk : ∀ i : Fin m, AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V m i ≫ k = k) :
    AlgebraicGeometry.Scheme.Modules.symPow V m ⟶ W :=
  CategoryTheory.Limits.wideCoequalizer.desc k (by
    have h : ∀ j : ULift.{u} (Option (Fin m)),
        (match j.down with
          | none => 𝟙 (AlgebraicGeometry.Scheme.Modules.monoidalPow V m)
          | some i => AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V m i) ≫ k = k := by
      rintro ⟨_ | i⟩
      · exact Category.id_comp k
      · exact hk i
    intro j₁ j₂
    exact (h j₁).trans (h j₂).symm)

/-- The tensor–Hom adjunction for the monoidal tensor product (transported from `Modules.tensor` along
`Modules.tensor ≅ ⊗`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv {X : AlgebraicGeometry.Scheme.{u}}
    (F G H : X.Modules) :
    (F ⊗ G ⟶ H) ≃ (F ⟶ AlgebraicGeometry.Scheme.Modules.internalHom G H) :=
  ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).homCongr (CategoryTheory.Iso.refl H)).symm.trans
    (AlgebraicGeometry.Scheme.Modules.tensorHomEquiv F G H)

namespace AlgebraicGeometry.Scheme.Modules

/-- The inverse of `tensorObjHomEquiv` is `ψ ↦ (ψ ▷ G) ≫ evaluation`. -/
theorem tensorObjHomEquiv_symm_apply {X : AlgebraicGeometry.Scheme.{u}} (F G H : X.Modules)
    (ψ : F ⟶ internalHom G H) :
    (tensorObjHomEquiv F G H).symm ψ = (ψ ▷ G) ≫ internalHomEval G H := by
  have e : (tensorHomEquiv F G H).symm ψ =
      (tensorIsoTensorObj F G).hom ≫ (ψ ▷ G) ≫ internalHomEval G H := rfl
  show ((tensorIsoTensorObj F G).homCongr (Iso.refl H)) ((tensorHomEquiv F G H).symm ψ) = _
  rw [e]
  simp [Iso.homCongr]

/-- Currying is natural in the first variable. -/
theorem tensorObjHomEquiv_naturality_left {X : AlgebraicGeometry.Scheme.{u}} {F' F : X.Modules}
    (G H : X.Modules) (a : F' ⟶ F) (f : F ⊗ G ⟶ H) :
    a ≫ tensorObjHomEquiv F G H f = tensorObjHomEquiv F' G H ((a ▷ G) ≫ f) := by
  apply (tensorObjHomEquiv F' G H).symm.injective
  rw [Equiv.symm_apply_apply, tensorObjHomEquiv_symm_apply, MonoidalCategory.comp_whiskerRight,
    Category.assoc, ← tensorObjHomEquiv_symm_apply, Equiv.symm_apply_apply]

instance symPowπ_epi {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m : ℕ) :
    Epi (symPowπ V m) :=
  ⟨fun _ _ w => CategoryTheory.Limits.wideCoequalizer.hom_ext w⟩

theorem symPowπ_desc {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m : ℕ) {W : X.Modules}
    (k : monoidalPow V m ⟶ W) (hk : ∀ i : Fin m, monoidalPowTransp V m i ≫ k = k) :
    symPowπ V m ≫ symPowDesc V m k hk = k :=
  CategoryTheory.Limits.wideCoequalizer.π_desc _ _

/-- The quotient map satisfies the coequalizing condition: an adjacent transposition followed by the quotient
map is the quotient map. -/
theorem monoidalPowTransp_symPowπ {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (N k : ℕ)
    (hk : k < N) : monoidalPowTransp V N k ≫ symPowπ V N = symPowπ V N := by
  have h := CategoryTheory.Limits.wideCoequalizer.condition
    (fun j : ULift.{u} (Option (Fin N)) =>
      match j.down with
      | none => 𝟙 (monoidalPow V N)
      | some i => monoidalPowTransp V N i) ⟨some ⟨k, hk⟩⟩ ⟨none⟩
  rw [Category.id_comp] at h
  exact h

/-- `π ▷ G` is an epimorphism (naturality of currying + `π` epi). -/
theorem symPowπ_whiskerRight_cancel {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m : ℕ)
    (G : X.Modules) {T : X.Modules} (x y : symPow V m ⊗ G ⟶ T)
    (h : (symPowπ V m ▷ G) ≫ x = (symPowπ V m ▷ G) ≫ y) : x = y := by
  apply (tensorObjHomEquiv _ _ _).injective
  rw [← cancel_epi (symPowπ V m), tensorObjHomEquiv_naturality_left,
    tensorObjHomEquiv_naturality_left, h]

/-- The computation rule for descent in one variable: `(π ▷ G) ≫ descent = original morphism`. -/
theorem symPowπ_whiskerRight_descCurry {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m : ℕ)
    (G : X.Modules) {T : X.Modules} (f : monoidalPow V m ⊗ G ⟶ T)
    (h : ∀ i : Fin m, monoidalPowTransp V m i ≫ tensorObjHomEquiv _ _ _ f = tensorObjHomEquiv _ _ _ f) :
    (symPowπ V m ▷ G) ≫
      (tensorObjHomEquiv _ _ _).symm (symPowDesc V m (tensorObjHomEquiv _ _ _ f) h) = f := by
  rw [tensorObjHomEquiv_symm_apply, ← MonoidalCategory.comp_whiskerRight_assoc, symPowπ_desc,
    ← tensorObjHomEquiv_symm_apply, Equiv.symm_apply_apply]

/-- The invariance needed for the second descent step of `symPowDesc₂`. -/
theorem symPowDesc₂_invariant₂ {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m n : ℕ)
    {T : X.Modules} (f : monoidalPow V m ⊗ monoidalPow V n ⟶ T)
    (hf₂ : ∀ j : Fin n, (monoidalPow V m ◁ monoidalPowTransp V n j) ≫ f = f)
    (h : ∀ i : Fin m, monoidalPowTransp V m i ≫ tensorObjHomEquiv _ _ _ f = tensorObjHomEquiv _ _ _ f)
    (j : Fin n) :
    monoidalPowTransp V n j ≫ tensorObjHomEquiv _ _ _ ((β_ _ _).hom ≫
        (tensorObjHomEquiv _ _ _).symm (symPowDesc V m (tensorObjHomEquiv _ _ _ f) h)) =
      tensorObjHomEquiv _ _ _ ((β_ _ _).hom ≫
        (tensorObjHomEquiv _ _ _).symm (symPowDesc V m (tensorObjHomEquiv _ _ _ f) h)) := by
  rw [tensorObjHomEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc]
  congr 1
  apply symPowπ_whiskerRight_cancel
  rw [← MonoidalCategory.whisker_exchange_assoc, symPowπ_whiskerRight_descCurry, hf₂]

end AlgebraicGeometry.Scheme.Modules

/-- Descent in two variables: a morphism `P_m ⊗ P_n → T` invariant under the adjacent transpositions on both
sides gives `Sym^m ⊗ Sym^n → T`. Method: curry, descend along the first quotient map, uncurry; swap sides by
the braiding, treat the second factor the same way, and swap back. (That `⊗` preserves colimits in each
variable is encoded in the currying `Hom(− ⊗ G, T) ≃ Hom(−, 𝓗om(G, T))`.)
The hypotheses `hf₁`, `hf₂` are necessary: for `X = Spec k`, `V` free of rank `2`, `m = 2`, `n = 0`,
`T = V^{⊗2}`, `f = ρ_.hom`, `curry f` is essentially the identity while `monoidalPowTransp V 2 0` is the
braiding `β_{V,V} ≠ 𝟙`, so `transp ≫ curry f ≠ curry f`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPowDesc₂ {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (f : AlgebraicGeometry.Scheme.Modules.monoidalPow V m ⊗ AlgebraicGeometry.Scheme.Modules.monoidalPow V n ⟶ T)
    (hf₁ : ∀ i : Fin m, (AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V m i ▷
      AlgebraicGeometry.Scheme.Modules.monoidalPow V n) ≫ f = f)
    (hf₂ : ∀ j : Fin n, (AlgebraicGeometry.Scheme.Modules.monoidalPow V m ◁
      AlgebraicGeometry.Scheme.Modules.monoidalPowTransp V n j) ≫ f = f) :
    AlgebraicGeometry.Scheme.Modules.symPow V m ⊗ AlgebraicGeometry.Scheme.Modules.symPow V n ⟶ T :=
  -- step 1: `Sym^m ⊗ P_n → T`
  let g : AlgebraicGeometry.Scheme.Modules.symPow V m ⊗ AlgebraicGeometry.Scheme.Modules.monoidalPow V n ⟶ T :=
    (AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv _ _ _).symm
      (AlgebraicGeometry.Scheme.Modules.symPowDesc V m
        (AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv _ _ _ f)
        (fun i => by
          rw [AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv_naturality_left, hf₁ i]))
  -- step 2: swap to `P_n ⊗ Sym^m → T`, descend along the quotient map of `P_n`, swap back
  let g' : AlgebraicGeometry.Scheme.Modules.monoidalPow V n ⊗ AlgebraicGeometry.Scheme.Modules.symPow V m ⟶ T :=
    (β_ _ _).hom ≫ g
  let h : AlgebraicGeometry.Scheme.Modules.symPow V n ⊗ AlgebraicGeometry.Scheme.Modules.symPow V m ⟶ T :=
    (AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv _ _ _).symm
      (AlgebraicGeometry.Scheme.Modules.symPowDesc V n
        (AlgebraicGeometry.Scheme.Modules.tensorObjHomEquiv _ _ _ g')
        (fun j => AlgebraicGeometry.Scheme.Modules.symPowDesc₂_invariant₂ V m n f hf₂ _ j))
  (β_ _ _).hom ≫ h

namespace AlgebraicGeometry.Scheme.Modules

private theorem monoidalPowTransp_succ_succ {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (n j : ℕ) :
  monoidalPowTransp V (n+1) (j+1) = monoidalPowTransp V n j ▷ V := by cases n <;> rfl

private theorem monoidalPowCat_succ_hom {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m n : ℕ) :
  (monoidalPowCat V m (n+1)).hom = (α_ (monoidalPow V m) (monoidalPow V n) V).inv ≫ (monoidalPowCat V m n).hom ▷ V := rfl

private theorem monoidalPowTransp_eq_id {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    ∀ (n j : ℕ), n ≤ j + 1 → monoidalPowTransp V n j = 𝟙 _
  | 0, _, _ => rfl
  | 1, 0, _ => rfl
  | n + 2, 0, h => absurd h (by omega)
  | n + 1, j + 1, h => by
    rw [monoidalPowTransp_succ_succ, monoidalPowTransp_eq_id V n j (by omega)]
    exact MonoidalCategory.id_whiskerRight _ _


section general
variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem aux_catR {A B Q : C} (V : C) (t : A ⟶ A) (c : A ⊗ B ⟶ Q) (t' : Q ⟶ Q)
    (ih : (t ▷ B) ≫ c = c ≫ t') :
    (t ▷ (B ⊗ V)) ≫ (α_ A B V).inv ≫ (c ▷ V) = ((α_ A B V).inv ≫ (c ▷ V)) ≫ (t' ▷ V) := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, ← ih,
    MonoidalCategory.comp_whiskerRight]
  simp

private theorem aux_catL {A B Q : C} (V : C) (t : B ⟶ B) (c : A ⊗ B ⟶ Q) (t' : Q ⟶ Q)
    (ih : (A ◁ t) ≫ c = c ≫ t') :
    (A ◁ (t ▷ V)) ≫ (α_ A B V).inv ≫ (c ▷ V) = ((α_ A B V).inv ≫ (c ▷ V)) ≫ (t' ▷ V) := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, ← ih,
    MonoidalCategory.comp_whiskerRight]
  simp

private theorem aux_catL0 {A B Q : C} (V : C) (b : V ⊗ V ⟶ V ⊗ V) (c : A ⊗ B ⟶ Q) :
    (A ◁ ((α_ B V V).hom ≫ (B ◁ b) ≫ (α_ B V V).inv)) ≫
        ((α_ A (B ⊗ V) V).inv ≫ ((α_ A B V).inv ≫ c ▷ V) ▷ V) =
      ((α_ A (B ⊗ V) V).inv ≫ ((α_ A B V).inv ≫ c ▷ V) ▷ V) ≫
        ((α_ Q V V).hom ≫ (Q ◁ b) ≫ (α_ Q V V).inv) := by
  have h1 : (c ▷ V ▷ V) ≫ (α_ Q V V).hom ≫ (Q ◁ b) ≫ (α_ Q V V).inv =
      (α_ (A ⊗ B) V V).hom ≫ ((A ⊗ B) ◁ b) ≫ (α_ (A ⊗ B) V V).inv ≫ (c ▷ V ▷ V) := by
    rw [MonoidalCategory.associator_naturality_left_assoc,
      ← MonoidalCategory.whisker_exchange_assoc,
      MonoidalCategory.associator_inv_naturality_left]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc, h1]
  simp only [← Category.assoc]
  congr 1
  monoidal

end general

theorem monoidalPowCat_whiskerRight_transp {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m i : ℕ) :
    ∀ (n : ℕ),
      (monoidalPowTransp V m i ▷ monoidalPow V n) ≫ (monoidalPowCat V m n).hom =
        (monoidalPowCat V m n).hom ≫ monoidalPowTransp V (m + n) (i + n)
  | 0 => by
    show (monoidalPowTransp V m i ▷ 𝟙_ X.Modules) ≫ (ρ_ (monoidalPow V m)).hom =
      (ρ_ (monoidalPow V m)).hom ≫ monoidalPowTransp V m i
    simp
  | n + 1 => by
    have ih := monoidalPowCat_whiskerRight_transp V m i n
    have e : monoidalPowTransp V (m + (n + 1)) (i + (n + 1)) =
      monoidalPowTransp V (m + n) (i + n) ▷ V := monoidalPowTransp_succ_succ V (m + n) (i + n)
    rw [e, monoidalPowCat_succ_hom]
    exact aux_catR V _ _ _ ih

theorem monoidalPowCat_whiskerLeft_transp {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (m : ℕ) :
    ∀ (n j : ℕ), j + 1 < n →
      (monoidalPow V m ◁ monoidalPowTransp V n j) ≫ (monoidalPowCat V m n).hom =
        (monoidalPowCat V m n).hom ≫ monoidalPowTransp V (m + n) j
  | 0, _, h => absurd h (by omega)
  | 1, _, h => absurd h (by omega)
  | n + 2, 0, _ => by
    have e : monoidalPowTransp V (m + (n + 2)) 0 =
      (α_ (monoidalPow V (m + n)) V V).hom ≫ (monoidalPow V (m + n) ◁ (β_ V V).hom) ≫
          (α_ (monoidalPow V (m + n)) V V).inv := rfl
    have e' : monoidalPowTransp V (n + 2) 0 =
      (α_ (monoidalPow V n) V V).hom ≫ (monoidalPow V n ◁ (β_ V V).hom) ≫
          (α_ (monoidalPow V n) V V).inv := rfl
    rw [e, e', monoidalPowCat_succ_hom, monoidalPowCat_succ_hom]
    exact aux_catL0 V _ _
  | n + 1, j + 1, h => by
    have ih := monoidalPowCat_whiskerLeft_transp V m n j (by omega)
    have e : monoidalPowTransp V (m + (n + 1)) (j + 1) =
      monoidalPowTransp V (m + n) j ▷ V := monoidalPowTransp_succ_succ V (m + n) j
    rw [e, monoidalPowCat_succ_hom, monoidalPowTransp_succ_succ]
    exact aux_catL V _ _ _ ih
end AlgebraicGeometry.Scheme.Modules

/-- The multiplication `Sym^m ⊗ Sym^n → Sym^{m+n}`: descended from `P_m ⊗ P_n ≅ P_{m+n} → Sym^{m+n}`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symPowMul {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.symPow V m ⊗ AlgebraicGeometry.Scheme.Modules.symPow V n ⟶
      AlgebraicGeometry.Scheme.Modules.symPow V (m + n) :=
  AlgebraicGeometry.Scheme.Modules.symPowDesc₂ V m n
    ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat V m n).hom ≫
      AlgebraicGeometry.Scheme.Modules.symPowπ V (m + n))
    (fun i => by
      rw [← Category.assoc, AlgebraicGeometry.Scheme.Modules.monoidalPowCat_whiskerRight_transp,
        Category.assoc, AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_symPowπ V (m + n) (i + n)
          (by omega)])
    (fun j => by
      by_cases hj : (j : ℕ) + 1 < n
      · rw [← Category.assoc,
          AlgebraicGeometry.Scheme.Modules.monoidalPowCat_whiskerLeft_transp V m n j hj,
          Category.assoc, AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_symPowπ V (m + n) j
            (by omega)]
      · rw [AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id V n j (by omega),
          MonoidalCategory.whiskerLeft_id, Category.id_comp])


/-! ## Epimorphy of the quotient maps and compatibility of `symPowMul` with them

The tensor–Hom adjunction `tensorObjHomEquiv` in `X.Modules` is natural in the first variable, so `f ▷ G`
preserves epimorphisms; via the braiding so does `G ◁ f`; hence `π_m ⊗ₘ π_n` is an epimorphism. `symPowMul` is
descended by `symPowDesc₂` along `(monoidalPowCat V m n).hom ≫ symPowπ V (m+n)`, so
`(π_m ⊗ₘ π_n) ≫ symPowMul V m n = (monoidalPowCat V m n).hom ≫ π_{m+n}`; the three monoidal laws reduce to the
tensor powers through these two facts. -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Right whiskering preserves epimorphisms (the tensor–Hom adjunction is natural in the first variable). -/
theorem epi_whiskerRight_of_epi {F' F : X.Modules} (f : F' ⟶ F) [Epi f] (G : X.Modules) :
    Epi (f ▷ G) := by
  refine ⟨fun {T} x y h => ?_⟩
  apply (tensorObjHomEquiv _ _ _).injective
  rw [← cancel_epi f, tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left, h]

/-- Left whiskering preserves epimorphisms (via the braiding, reduce to right whiskering). -/
theorem epi_whiskerLeft_of_epi (G : X.Modules) {F' F : X.Modules} (f : F' ⟶ F) [Epi f] :
    Epi (G ◁ f) := by
  have e : G ◁ f = (β_ G F').hom ≫ (f ▷ G) ≫ (β_ G F).inv := by
    rw [← BraidedCategory.braiding_naturality_right_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  have := epi_whiskerRight_of_epi f G
  infer_instance

/-- The tensor product of two epimorphisms is an epimorphism. -/
theorem epi_tensorHom_of_epi {F' F G' G : X.Modules} (f : F' ⟶ F) (g : G' ⟶ G) [Epi f] [Epi g] :
    Epi (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def]
  have := epi_whiskerRight_of_epi f G'
  have := epi_whiskerLeft_of_epi F g
  infer_instance

/-- The computation rule for descent in two variables: `(π_m ⊗ₘ π_n) ≫ symPowDesc₂ f = f`. -/
theorem tensorHom_symPowπ_symPowDesc₂ (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (f : monoidalPow V m ⊗ monoidalPow V n ⟶ T)
    (hf₁ : ∀ i : Fin m, (monoidalPowTransp V m i ▷ monoidalPow V n) ≫ f = f)
    (hf₂ : ∀ j : Fin n, (monoidalPow V m ◁ monoidalPowTransp V n j) ≫ f = f) :
    (symPowπ V m ⊗ₘ symPowπ V n) ≫ symPowDesc₂ V m n f hf₁ hf₂ = f := by
  unfold symPowDesc₂
  simp only []
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    BraidedCategory.braiding_naturality_right_assoc, symPowπ_whiskerRight_descCurry,
    SymmetricCategory.symmetry_assoc, symPowπ_whiskerRight_descCurry]

/-- `symPowMul` is compatible with the quotient maps:
`(π_m ⊗ₘ π_n) ≫ symPowMul V m n = (monoidalPowCat V m n).hom ≫ π_{m+n}`. -/
@[reassoc]
theorem tensorHom_symPowπ_symPowMul (V : X.Modules) (m n : ℕ) :
    (symPowπ V m ⊗ₘ symPowπ V n) ≫ symPowMul V m n =
      (monoidalPowCat V m n).hom ≫ symPowπ V (m + n) :=
  tensorHom_symPowπ_symPowDesc₂ V m n _ _ _

/-- Cancellation along `π_m ⊗ₘ π_n`. -/
theorem symPowπ_tensorHom_cancel (V : X.Modules) (m n : ℕ) {T : X.Modules}
    (x y : symPow V m ⊗ symPow V n ⟶ T)
    (h : (symPowπ V m ⊗ₘ symPowπ V n) ≫ x = (symPowπ V m ⊗ₘ symPowπ V n) ≫ y) : x = y := by
  have := epi_tensorHom_of_epi (symPowπ V m) (symPowπ V n)
  exact (cancel_epi _).mp h

/-- The quotient maps commute with the index transport `eqToHom`. -/
theorem symPowπ_comp_eqToHom (V : X.Modules) {a b : ℕ} (h : a = b) :
    symPowπ V a ≫ eqToHom (congrArg (symPow V) h) =
      eqToHom (congrArg (monoidalPow V) h) ≫ symPowπ V b := by
  subst h; simp

end AlgebraicGeometry.Scheme.Modules

/- The four proof obligations of `symGradedAlgebraOfQC` (quasi-coherence and the three algebra laws) are stated
   as named theorems below; the data are `symPow` / `symPowMul` / `symPowπ V 0`. -/

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The structure sheaf `𝟙_ X.Modules = O_X` is quasi-coherent: `O_X ≅ free PUnit` (the coproduct over a point),
free sheaves are locally free hence quasi-coherent (Mathlib
`SheafOfModules.instIsQuasicoherentOfIsLocallyFree`), and quasi-coherence is invariant under isomorphism. -/
theorem isQuasicoherent_tensorUnit (X : AlgebraicGeometry.Scheme.{u}) :
    (𝟙_ X.Modules).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
    (SheafOfModules.instIsQuasicoherentOfIsLocallyFree (SheafOfModules.free PUnit.{u + 1}))

/-- The zero sheaf of modules is quasi-coherent: `free PEmpty` is initial (`Hom(free ∅, M) ≃ (∅ → Γ(M))` is a
point), hence a zero object, isomorphic to `0`; free sheaves are quasi-coherent and quasi-coherence is
invariant under isomorphism. -/
theorem isQuasicoherent_zero (X : AlgebraicGeometry.Scheme.{u}) :
    (0 : X.Modules).IsQuasicoherent := by
  have hinit : CategoryTheory.Limits.IsInitial (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) :=
    CategoryTheory.Limits.IsInitial.ofUniqueHom
      (fun M => (SheafOfModules.freeHomEquiv M).symm (fun i => i.elim))
      (fun M f => (SheafOfModules.freeHomEquiv M).injective (funext fun i => i.elim))
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (hinit.uniqueUpToIso (CategoryTheory.Limits.isZero_zero _).isInitial)
    (SheafOfModules.instIsQuasicoherentOfIsLocallyFree (SheafOfModules.free PEmpty.{u + 1}))

/-- The monoidal tensor product preserves quasi-coherence (Stacks 01CE, transported along `tensor F G ≅ F ⊗ G`). -/
theorem isQuasicoherent_tensorObj (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (tensorIsoTensorObj F G)
    (isQuasicoherent_tensor F G)

/-- Tensor powers preserve quasi-coherence (induction on `m`). -/
theorem monoidalPow_isQuasicoherent (V : X.Modules) (hV : V.IsQuasicoherent) :
    ∀ m : ℕ, (monoidalPow V m).IsQuasicoherent
  | 0 => isQuasicoherent_tensorUnit X
  | m + 1 =>
    haveI := monoidalPow_isQuasicoherent V hV m
    isQuasicoherent_tensorObj (monoidalPow V m) V

end AlgebraicGeometry.Scheme.Modules

/-- `Sym^m V` is quasi-coherent: `Sym^m V` is a quotient (cokernel) of `V^{⊗m}`; Stacks 01CE (tensor products
preserve quasi-coherence) + 01ID (cokernels preserve quasi-coherence). `V^{⊗m}` is quasi-coherent by
`monoidalPow_isQuasicoherent`; the wide coequalizer is a colimit over `WalkingParallelFamily`, handled by
`isQuasicoherent_colimit`. -/
theorem AlgebraicGeometry.Scheme.Modules.symPow_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (_hV : V.IsQuasicoherent) (m : ℕ) : (AlgebraicGeometry.Scheme.Modules.symPow V m).IsQuasicoherent :=
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_colimit _ (fun j => by
    cases j <;> exact AlgebraicGeometry.Scheme.Modules.monoidalPow_isQuasicoherent V _hV m)

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

section general
variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem aux_one_mul {P S T U Q : C} (π0 : 𝟙_ C ⟶ S) (πm : P ⟶ T) (mul : S ⊗ T ⟶ U)
    (c : 𝟙_ C ⊗ P ⟶ Q) (πq : Q ⟶ U) (h : (π0 ⊗ₘ πm) ≫ mul = c ≫ πq) (e : T ⟶ U)
    (hc : c ≫ πq = (λ_ P).hom ≫ πm ≫ e) [Epi (𝟙_ C ◁ πm)] :
    (π0 ▷ T) ≫ mul = (λ_ T).hom ≫ e := by
  rw [← cancel_epi (𝟙_ C ◁ πm), ← Category.assoc, ← MonoidalCategory.tensorHom_def', h, hc,
    MonoidalCategory.leftUnitor_naturality_assoc]

private theorem aux_unit_left (V : C) {P Q : C} (e : P ⟶ Q) (e' : P ⊗ V ⟶ Q ⊗ V) (he : e ▷ V = e') :
    (α_ (𝟙_ C) P V).inv ≫ ((λ_ P).hom ≫ e) ▷ V = (λ_ (P ⊗ V)).hom ≫ e' := by
  subst he
  rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.leftUnitor_tensor_hom, Category.assoc]

end general

/-- `monoidalPowCat V 0 m` is the left unitor (followed by the index transport `m = 0 + m`). By induction on `m`:
`m = 0` is `unitors_equal`, `m + 1` uses `leftUnitor_tensor`. -/
theorem monoidalPowCat_zero_left (V : X.Modules) :
    ∀ m : ℕ, (monoidalPowCat V 0 m).hom =
      (λ_ (monoidalPow V m)).hom ≫ eqToHom (congrArg (monoidalPow V) (Nat.zero_add m).symm)
  | 0 => by
    have e : eqToHom (congrArg (monoidalPow V) (Nat.zero_add 0).symm) = 𝟙 (monoidalPow V 0) := rfl
    rw [e, Category.comp_id]
    exact (MonoidalCategory.unitors_equal).symm
  | m + 1 => by
    rw [monoidalPowCat_succ_hom, monoidalPowCat_zero_left V m]
    exact aux_unit_left V _ _ (by rw [MonoidalCategory.eqToHom_whiskerRight]; rfl)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

section general
variable {C : Type*} [Category C] [MonoidalCategory C]

private theorem aux_assoc0 {A B Q : C} (c : A ⊗ B ⟶ Q) (e : Q ⟶ Q) (he : e = 𝟙 Q) :
    (α_ A B (𝟙_ C)).hom ≫ (A ◁ (ρ_ B).hom) ≫ c = (c ▷ 𝟙_ C) ≫ (ρ_ Q).hom ≫ e := by
  subst he
  rw [Category.comp_id, ← Category.assoc, ← MonoidalCategory.rightUnitor_tensor_hom,
    MonoidalCategory.rightUnitor_naturality]

private theorem aux_assoc_succ {A B P Q R S R' : C} (V : C) (c_np : B ⊗ P ⟶ Q) (c_mnp : A ⊗ Q ⟶ R)
    (c_mn : A ⊗ B ⟶ S) (c_mn_p : S ⊗ P ⟶ R') (e : R' ⟶ R)
    (ih : (α_ A B P).hom ≫ (A ◁ c_np) ≫ c_mnp = (c_mn ▷ P) ≫ c_mn_p ≫ e)
    (e' : R' ⊗ V ⟶ R ⊗ V) (he : e ▷ V = e') :
    (α_ A B (P ⊗ V)).hom ≫ (A ◁ ((α_ B P V).inv ≫ c_np ▷ V)) ≫ (α_ A Q V).inv ≫ (c_mnp ▷ V) =
      (c_mn ▷ (P ⊗ V)) ≫ (α_ S P V).inv ≫ (c_mn_p ▷ V) ≫ e' := by
  subst he
  have h1 : (α_ A B (P ⊗ V)).hom ≫ (A ◁ (α_ B P V).inv) ≫ (α_ A (B ⊗ P) V).inv =
      (α_ (A ⊗ B) P V).inv ≫ ((α_ A B P).hom ▷ V) := by monoidal
  have ih' := congrArg (fun t => t ▷ V) ih
  simp only [MonoidalCategory.comp_whiskerRight] at ih'
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.associator_inv_naturality_middle_assoc,
    MonoidalCategory.associator_inv_naturality_left_assoc, ← ih']
  slice_lhs 1 3 => rw [h1]
  simp only [Category.assoc]

end general

theorem eqToHom_whiskerRight_succ (V : X.Modules) {a b : ℕ} (h : a = b) :
    (eqToHom (congrArg (monoidalPow V) h) ▷ V) =
      eqToHom (congrArg (fun Z : X.Modules => Z ⊗ V) (congrArg (monoidalPow V) h)) := by
  subst h; simp

theorem eqToHom_comp_eqToHom_symm (V : X.Modules) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (monoidalPow V) h) ≫ eqToHom (congrArg (monoidalPow V) h.symm) = 𝟙 _ := by
  subst h; simp

theorem eqToHom_trans_monoidalPow (V : X.Modules) {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    eqToHom (congrArg (monoidalPow V) (h₁.trans h₂)) =
      eqToHom (congrArg (monoidalPow V) h₁) ≫ eqToHom (congrArg (monoidalPow V) h₂) := by
  subst h₁ h₂; simp

/-- Associativity of the concatenation isomorphisms (induction on `p`: `p = 0` is `rightUnitor_tensor_hom` +
naturality of the right unitor; `p + 1` is the pentagon + naturality of the associator + the induction
hypothesis whiskered on the right by `V`). -/
@[reassoc]
theorem monoidalPowCat_assoc (V : X.Modules) (m n : ℕ) : ∀ p : ℕ,
    (α_ (monoidalPow V m) (monoidalPow V n) (monoidalPow V p)).hom ≫
        (monoidalPow V m ◁ (monoidalPowCat V n p).hom) ≫ (monoidalPowCat V m (n + p)).hom =
      ((monoidalPowCat V m n).hom ▷ monoidalPow V p) ≫ (monoidalPowCat V (m + n) p).hom ≫
        eqToHom (congrArg (monoidalPow V) (Nat.add_assoc m n p))
  | 0 => by
    -- first rewrite the goal with `show`/`rfl` into literally the shape of `aux_assoc0`, then `exact`:
    -- otherwise the unifier unfolds `≫`, `α_` down to the presheaf level (5 s → < 1 s)
    have e₁ : (monoidalPowCat V n 0).hom = (ρ_ (monoidalPow V n)).hom := rfl
    have e₂ : (monoidalPowCat V (m + n) 0).hom = (ρ_ (monoidalPow V (m + n))).hom := rfl
    have e₃ : eqToHom (congrArg (monoidalPow V) (Nat.add_assoc m n 0)) =
      𝟙 (monoidalPow V (m + n)) := rfl
    show (α_ (monoidalPow V m) (monoidalPow V n) (𝟙_ X.Modules)).hom ≫
        (monoidalPow V m ◁ (monoidalPowCat V n 0).hom) ≫ (monoidalPowCat V m n).hom =
      ((monoidalPowCat V m n).hom ▷ 𝟙_ X.Modules) ≫ (monoidalPowCat V (m + n) 0).hom ≫
        eqToHom (congrArg (monoidalPow V) (Nat.add_assoc m n 0))
    rw [e₁, e₂, e₃]
    exact aux_assoc0 (monoidalPowCat V m n).hom (𝟙 _) rfl
  | p + 1 => by
    -- as above: all indices in `succ` form, `monoidalPow V (p+1)` as `monoidalPow V p ⊗ V`, then `rw` to a literal match
    show (α_ (monoidalPow V m) (monoidalPow V n) (monoidalPow V p ⊗ V)).hom ≫
        (monoidalPow V m ◁ (monoidalPowCat V n (p + 1)).hom) ≫ (monoidalPowCat V m (n + p + 1)).hom =
      ((monoidalPowCat V m n).hom ▷ (monoidalPow V p ⊗ V)) ≫ (monoidalPowCat V (m + n) (p + 1)).hom ≫
        eqToHom (congrArg (fun Z : X.Modules => Z ⊗ V)
          (congrArg (monoidalPow V) (Nat.add_assoc m n p)))
    rw [monoidalPowCat_succ_hom V n p, monoidalPowCat_succ_hom V m (n + p),
      monoidalPowCat_succ_hom V (m + n) p]
    exact aux_assoc_succ V (monoidalPowCat V n p).hom (monoidalPowCat V m (n + p)).hom
      (monoidalPowCat V m n).hom (monoidalPowCat V (m + n) p).hom
      (eqToHom (congrArg (monoidalPow V) (Nat.add_assoc m n p))) (monoidalPowCat_assoc V m n p)
      _ (eqToHom_whiskerRight_succ V (Nat.add_assoc m n p))

/-- Transposition words: finite composites of adjacent transpositions. -/
inductive IsTranspWord (V : X.Modules) : (N : ℕ) → (monoidalPow V N ⟶ monoidalPow V N) → Prop
  | id (N : ℕ) : IsTranspWord V N (𝟙 _)
  | transp (N i : ℕ) : IsTranspWord V N (monoidalPowTransp V N i)
  | comp {N : ℕ} {w w' : monoidalPow V N ⟶ monoidalPow V N} :
      IsTranspWord V N w → IsTranspWord V N w' → IsTranspWord V N (w ≫ w')

theorem IsTranspWord.comp_symPowπ {V : X.Modules} {N : ℕ} {w : monoidalPow V N ⟶ monoidalPow V N}
    (h : IsTranspWord V N w) : w ≫ symPowπ V N = symPowπ V N := by
  induction h with
  | id => exact Category.id_comp _
  | transp i =>
    by_cases hi : i < N
    · exact monoidalPowTransp_symPowπ V _ i hi
    · rw [monoidalPowTransp_eq_id V _ i (by omega), Category.id_comp]
  | comp _ _ ih1 ih2 => rw [Category.assoc, ih2, ih1]

theorem IsTranspWord.whiskerRight {V : X.Modules} {N : ℕ} {w : monoidalPow V N ⟶ monoidalPow V N}
    (h : IsTranspWord V N w) : IsTranspWord V (N + 1) (w ▷ V) := by
  induction h with
  | id => rw [MonoidalCategory.id_whiskerRight]; exact .id _
  | transp i => rw [← monoidalPowTransp_succ_succ]; exact .transp _ (i + 1)
  | comp _ _ ih1 ih2 => rw [MonoidalCategory.comp_whiskerRight]; exact .comp ih1 ih2

theorem IsTranspWord.eqToHom_conj {V : X.Modules} {N N' : ℕ} (h : N = N')
    {w : monoidalPow V N ⟶ monoidalPow V N} (hw : IsTranspWord V N w) :
    IsTranspWord V N' (eqToHom (congrArg (monoidalPow V) h.symm) ≫ w ≫
      eqToHom (congrArg (monoidalPow V) h)) := by
  subst h
  simpa using hw

theorem IsTranspWord.exists_whiskerLeft_cat {V : X.Modules} (k : ℕ) {N : ℕ}
    {w : monoidalPow V N ⟶ monoidalPow V N} (h : IsTranspWord V N w) :
    ∃ w' : monoidalPow V (k + N) ⟶ monoidalPow V (k + N), IsTranspWord V (k + N) w' ∧
      (monoidalPow V k ◁ w) ≫ (monoidalPowCat V k N).hom = (monoidalPowCat V k N).hom ≫ w' := by
  induction h with
  | id => exact ⟨𝟙 _, .id _, by rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id]⟩
  | transp i =>
    by_cases hi : i + 1 < N
    · exact ⟨_, .transp _ i, monoidalPowCat_whiskerLeft_transp V k _ i hi⟩
    · refine ⟨𝟙 _, .id _, ?_⟩
      rw [monoidalPowTransp_eq_id V _ i (by omega), MonoidalCategory.whiskerLeft_id, Category.id_comp,
        Category.comp_id]
  | comp _ _ ih1 ih2 =>
    obtain ⟨w₁, hw₁, e₁⟩ := ih1
    obtain ⟨w₂, hw₂, e₂⟩ := ih2
    exact ⟨w₁ ≫ w₂, .comp hw₁ hw₂, by
      rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, e₂, ← Category.assoc, e₁, Category.assoc]⟩

/-- The concatenation isomorphisms are natural in the index transport:
`(P_k ◁ eqToHom) ≫ cat k b = cat k a ≫ eqToHom`. -/
theorem whiskerLeft_eqToHom_monoidalPowCat (V : X.Modules) (k : ℕ) {a b : ℕ} (h : a = b) :
    (monoidalPow V k ◁ eqToHom (congrArg (monoidalPow V) h)) ≫ (monoidalPowCat V k b).hom =
      (monoidalPowCat V k a).hom ≫ eqToHom (congrArg (monoidalPow V) (congrArg (k + ·) h)) := by
  subst h; simp

theorem eqToHom_whiskerRight_comp_eqToHom_succ (V : X.Modules) {a b : ℕ} (h : a = b) :
    (eqToHom (congrArg (monoidalPow V) h) ▷ V) ≫
      eqToHom (congrArg (monoidalPow V) (congrArg Nat.succ h.symm)) = 𝟙 _ := by
  subst h; simp; rfl

section general
variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]

private theorem aux_rot0 (V : C) (e : (𝟙_ C ⊗ V) ⟶ (𝟙_ C ⊗ V)) (he : e = 𝟙 _) :
    (β_ (𝟙_ C) V).hom ≫ ((λ_ V).inv ▷ 𝟙_ C) ≫ (ρ_ (𝟙_ C ⊗ V)).hom ≫ e = 𝟙 _ := by
  subst he
  rw [Category.comp_id, MonoidalCategory.rightUnitor_naturality, braiding_rightUnitor_assoc,
    Iso.hom_inv_id]

private theorem aux_rot_succ (A V : C) {Q : C} (c : (𝟙_ C ⊗ V) ⊗ A ⟶ Q) (e : Q ⟶ A ⊗ V)
    (e' : Q ⊗ V ⟶ (A ⊗ V) ⊗ V) (he : e ▷ V = e') :
    (β_ (A ⊗ V) V).hom ≫ ((λ_ V).inv ▷ (A ⊗ V)) ≫ ((α_ (𝟙_ C ⊗ V) A V).inv ≫ (c ▷ V)) ≫ e' =
      ((α_ A V V).hom ≫ (A ◁ (β_ V V).hom) ≫ (α_ A V V).inv) ≫
        ((β_ A V).hom ≫ ((λ_ V).inv ▷ A) ≫ c ≫ e) ▷ V := by
  subst he
  have hβ : (β_ (A ⊗ V) V).hom = (α_ A V V).hom ≫ (A ◁ (β_ V V).hom) ≫ (α_ A V V).inv ≫
      ((β_ A V).hom ▷ V) ≫ (α_ V A V).hom := by
    rw [← BraidedCategory.hexagon_reverse_assoc]
    simp
  rw [hβ]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  congr 3
  rw [MonoidalCategory.associator_inv_naturality_left_assoc, Iso.hom_inv_id_assoc]

private theorem aux_swap0 (A : C) {Q : C} (c0 : 𝟙_ C ⊗ A ⟶ Q) (e : A ⟶ Q) (hc : c0 = (λ_ A).hom ≫ e)
    (e' : Q ⟶ A) (hee : e ≫ e' = 𝟙 A) :
    (ρ_ A).inv ≫ (β_ A (𝟙_ C)).hom ≫ c0 ≫ e' = 𝟙 A := by
  subst hc
  rw [Category.assoc, hee, Category.comp_id, braiding_leftUnitor, Iso.inv_hom_id]

private theorem aux_swap_succ {A B V M N R T U : C} (cmn : A ⊗ B ≅ M) (cnm : B ⊗ A ⟶ N) (E₁ : N ⟶ M)
    (c1m : (𝟙_ C ⊗ V) ⊗ A ⟶ R) (E₂ : R ⟶ A ⊗ V) (E₂' : A ⊗ V ⟶ R) (hE₂ : E₂ ≫ E₂' = 𝟙 R)
    (cn1m : B ⊗ R ⟶ T) (cn1_m : (B ⊗ V) ⊗ A ⟶ U) (E₃ : U ⟶ T) (E₄ : U ⟶ M ⊗ V) (E₆ : T ⟶ M ⊗ V)
    (hE₄ : E₄ = E₃ ≫ E₆)
    (hassoc : (α_ B (𝟙_ C ⊗ V) A).hom ≫ (B ◁ c1m) ≫ cn1m =
      (((α_ B (𝟙_ C) V).inv ≫ (ρ_ B).hom ▷ V) ▷ A) ≫ cn1_m ≫ E₃)
    (monoidalPowRot : A ⊗ V ⟶ A ⊗ V) (hrot : monoidalPowRot = (β_ A V).hom ≫ ((λ_ V).inv ▷ A) ≫ c1m ≫ E₂)
    (w' : N ⊗ V ⟶ N ⊗ V)
    (hw' : (B ◁ monoidalPowRot) ≫ ((α_ B A V).inv ≫ cnm ▷ V) = ((α_ B A V).inv ≫ cnm ▷ V) ≫ w')
    (E₅' : N ⊗ V ⟶ T) (hE₅ : (B ◁ E₂') ≫ cn1m = ((α_ B A V).inv ≫ cnm ▷ V) ≫ E₅')
    (F₁ : M ⊗ V ⟶ N ⊗ V) (hF₁ : (E₁ ▷ V) ≫ F₁ = 𝟙 _) (F₂ : N ⊗ V ⟶ M ⊗ V) (hF₂ : E₅' ≫ E₆ = F₂) :
    ((cmn.inv ▷ V) ≫ (α_ A B V).hom) ≫ (β_ A (B ⊗ V)).hom ≫ cn1_m ≫ E₄ =
      ((cmn.inv ≫ (β_ A B).hom ≫ cnm ≫ E₁) ▷ V) ≫ F₁ ≫ w' ≫ F₂ := by
  subst hE₄ hrot hF₂
  -- solve for `cn1_m ≫ E₃` using `hassoc`
  have hc : cn1_m ≫ E₃ = ((B ◁ (λ_ V).inv) ▷ A) ≫ (α_ B (𝟙_ C ⊗ V) A).hom ≫ (B ◁ c1m) ≫ cn1m := by
    rw [hassoc, MonoidalCategory.triangle_assoc_comp_right, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  have hβ : (α_ A B V).hom ≫ (β_ A (B ⊗ V)).hom =
      ((β_ A B).hom ▷ V) ≫ (α_ B A V).hom ≫ (B ◁ (β_ A V).hom) ≫ (α_ B V A).inv := by
    rw [← BraidedCategory.hexagon_forward_assoc, Iso.hom_inv_id, Category.comp_id]
  calc ((cmn.inv ▷ V) ≫ (α_ A B V).hom) ≫ (β_ A (B ⊗ V)).hom ≫ cn1_m ≫ E₃ ≫ E₆
      = (cmn.inv ▷ V) ≫ ((α_ A B V).hom ≫ (β_ A (B ⊗ V)).hom) ≫ (cn1_m ≫ E₃) ≫ E₆ := by
        simp only [Category.assoc]
    _ = (cmn.inv ▷ V) ≫ ((β_ A B).hom ▷ V) ≫ (α_ B A V).hom ≫
          (B ◁ ((β_ A V).hom ≫ ((λ_ V).inv ▷ A) ≫ c1m)) ≫ cn1m ≫ E₆ := by
        rw [hβ, hc]
        simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp]
        rw [← MonoidalCategory.associator_inv_naturality_middle_assoc, Iso.inv_hom_id_assoc]
    _ = (cmn.inv ▷ V) ≫ ((β_ A B).hom ▷ V) ≫ (α_ B A V).hom ≫
          (B ◁ ((β_ A V).hom ≫ ((λ_ V).inv ▷ A) ≫ c1m ≫ E₂)) ≫ (B ◁ E₂') ≫ cn1m ≫ E₆ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc B E₂ E₂', hE₂, MonoidalCategory.whiskerLeft_id,
          Category.id_comp]
    _ = (cmn.inv ▷ V) ≫ ((β_ A B).hom ▷ V) ≫ (α_ B A V).hom ≫
          ((α_ B A V).inv ≫ cnm ▷ V) ≫ w' ≫ E₅' ≫ E₆ := by
        simp only [Category.assoc]
        rw [reassoc_of% hE₅]
        try simp only [Category.assoc]
        rw [reassoc_of% hw']
        try simp only [Category.assoc]
    _ = ((cmn.inv ≫ (β_ A B).hom ≫ cnm ≫ E₁) ▷ V) ≫ F₁ ≫ w' ≫ E₅' ≫ E₆ := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Category.assoc (E₁ ▷ V), hF₁, Category.id_comp]

end general

/-- Rotation: move the last factor of `V^{⊗(m+1)}` to the front (via the braiding `β_{P_m,V}` and the
concatenation `P_1 ⊗ P_m ≅ P_{1+m}`). -/
def monoidalPowRot (V : X.Modules) (m : ℕ) : monoidalPow V (m + 1) ⟶ monoidalPow V (m + 1) :=
  (β_ (monoidalPow V m) V).hom ≫ ((λ_ V).inv ▷ monoidalPow V m) ≫ (monoidalPowCat V 1 m).hom ≫
    eqToHom (congrArg (monoidalPow V) (Nat.add_comm 1 m))

theorem isTranspWord_monoidalPowRot (V : X.Modules) : ∀ m : ℕ, IsTranspWord V (m + 1) (monoidalPowRot V m)
  | 0 => by
    have e : monoidalPowRot V 0 = 𝟙 _ := aux_rot0 V _ rfl
    rw [e]; exact .id _
  | m + 1 => by
    have e : monoidalPowRot V (m + 1) = monoidalPowTransp V (m + 2) 0 ≫ (monoidalPowRot V m ▷ V) :=
      aux_rot_succ (monoidalPow V m) V (monoidalPowCat V 1 m).hom _ _
        (eqToHom_whiskerRight_succ V (Nat.add_comm 1 m))
    rw [e]
    exact .comp (.transp _ 0) (isTranspWord_monoidalPowRot V m).whiskerRight

/-- The block swap `σ_{m,n} : P_{m+n} → P_{m+n}`. -/
def monoidalPowBlockSwap (V : X.Modules) (m n : ℕ) : monoidalPow V (m + n) ⟶ monoidalPow V (m + n) :=
  (monoidalPowCat V m n).inv ≫ (β_ (monoidalPow V m) (monoidalPow V n)).hom ≫
    (monoidalPowCat V n m).hom ≫ eqToHom (congrArg (monoidalPow V) (Nat.add_comm n m))

theorem isTranspWord_monoidalPowBlockSwap (V : X.Modules) (m : ℕ) : ∀ n : ℕ, IsTranspWord V (m + n) (monoidalPowBlockSwap V m n)
  | 0 => by
    have e : monoidalPowBlockSwap V m 0 = 𝟙 _ :=
      aux_swap0 (monoidalPow V m) (monoidalPowCat V 0 m).hom _ (monoidalPowCat_zero_left V m) _
        (by rw [eqToHom_trans]; rfl)
    rw [e]; exact .id _
  | n + 1 => by
    obtain ⟨w', hw', e⟩ := (isTranspWord_monoidalPowRot V m).exists_whiskerLeft_cat n
    have h : n + (m + 1) = m + (n + 1) := by omega
    have key : monoidalPowBlockSwap V m (n + 1) = (monoidalPowBlockSwap V m n ▷ V) ≫
        (eqToHom (congrArg (monoidalPow V) h.symm) ≫ w' ≫ eqToHom (congrArg (monoidalPow V) h)) :=
      aux_swap_succ (monoidalPowCat V m n) (monoidalPowCat V n m).hom _ (monoidalPowCat V 1 m).hom
        (eqToHom (congrArg (monoidalPow V) (Nat.add_comm 1 m)))
        (eqToHom (congrArg (monoidalPow V) (Nat.add_comm 1 m).symm))
        (eqToHom_comp_eqToHom_symm V (Nat.add_comm 1 m))
        (monoidalPowCat V n (1 + m)).hom (monoidalPowCat V (n + 1) m).hom
        (eqToHom (congrArg (monoidalPow V) (Nat.add_assoc n 1 m))) _
        (eqToHom (congrArg (monoidalPow V) (show n + (1 + m) = m + (n + 1) by omega)))
        (eqToHom_trans_monoidalPow V (Nat.add_assoc n 1 m) (show n + (1 + m) = m + (n + 1) by omega))
        (monoidalPowCat_assoc V n 1 m) (monoidalPowRot V m) rfl w' e
        (eqToHom (congrArg (monoidalPow V) (congrArg (n + ·) (Nat.add_comm m 1))))
        (whiskerLeft_eqToHom_monoidalPowCat V n (Nat.add_comm m 1)) _
        (eqToHom_whiskerRight_comp_eqToHom_succ V (Nat.add_comm n m)) _
        (eqToHom_trans_monoidalPow V (congrArg (n + ·) (Nat.add_comm m 1))
          (show n + (1 + m) = m + (n + 1) by omega)).symm
    rw [key]
    exact .comp (isTranspWord_monoidalPowBlockSwap V m n).whiskerRight (hw'.eqToHom_conj h)


/-- The block swap is invariant under the quotient map: `β_{V^{⊗m}, V^{⊗n}}` followed by the concatenation
`V^{⊗n} ⊗ V^{⊗m} ≅ V^{⊗(n+m)}` and the quotient to `Sym^{n+m}` equals concatenating
`V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗(m+n)}`, transporting the index, and taking the quotient.

Reference: Stacks 01CF (`Sym^n` is the `S_n`-coinvariants of `T^n`).

Proof: write `P_k = V^{⊗k}` and `σ_{m,n} := (cat m n)⁻¹ ≫ β ≫ (cat n m) ≫ eqToHom : P_{m+n} → P_{m+n}`. We show
`σ_{m,n} ≫ π = π`. By definition `π` coequalizes every adjacent transposition `transp (m+n) i`
(`monoidalPowTransp_symPowπ`), so it suffices that `σ_{m,n}` is a composite of adjacent transpositions (a
"transposition word").
1. Define the inductive predicate `IsTranspWord N : (P_N ⟶ P_N) → Prop`: `𝟙`, `transp N i`, composites. Lemmas:
   (a) `IsTranspWord N w → w ≫ π_N = π_N` (induction on the word);
   (b) `IsTranspWord N w → IsTranspWord (N+1) (w ▷ V)` (`monoidalPowTransp_succ_succ`:
       `transp (N+1) (i+1) = transp N i ▷ V`);
   (c) `IsTranspWord N w → IsTranspWord (k+N) ((P_k ◁ w) conjugated by cat k N)`
       (`monoidalPowCat_whiskerLeft_transp`, letter by letter; out-of-range letters at the end are `𝟙`);
   (d) transport along `eqToHom (N = N')` (`subst`).
2. The rotation `rot_m := β_{P_m,V} ≫ ((λ_ V).inv ▷ P_m) ≫ (cat 1 m).hom ≫ eqToHom : P_{m+1} → P_{m+1}` (move the
   last factor to the front) is a transposition word: for `m = 0` it is `𝟙` (`braiding_rightUnitor`); for
   `m+1`, `hexagon_reverse` gives `rot_{m+1} = transp (m+2) 0 ≫ (rot_m ▷ V)`, and (b) applies.
3. Induction on `n` for `σ_{m,n}`: for `n = 0`, `σ = 𝟙` (`monoidalPowCat_zero_left`, `braiding_leftUnitor`); for
   `n+1`, `hexagon_forward` splits `β_{P_m, P_n ⊗ V}`, `monoidalPowCat_assoc` (with `m := n, n := 1, p := m`)
   replaces `cat (n+1) m` by `cat n (1+m)`, giving
   `σ_{m,n+1} = (σ_{m,n} ▷ V) ≫ [(P_n ◁ rot_m) conjugated by cat n (m+1)]`, a transposition word by (b)(c)(d).
4. Conclude by (a).
Formalized along this route (`IsTranspWord`, `monoidalPowRot`, `monoidalPowBlockSwap`, and the variable-level
lemmas `aux_rot0` / `aux_rot_succ` / `aux_swap0` / `aux_swap_succ`). -/
theorem braiding_monoidalPowCat_symPowπ (V : X.Modules) (m n : ℕ) :
    (β_ (monoidalPow V m) (monoidalPow V n)).hom ≫ (monoidalPowCat V n m).hom ≫ symPowπ V (n + m) =
      (monoidalPowCat V m n).hom ≫ eqToHom (congrArg (monoidalPow V) (Nat.add_comm m n)) ≫
        symPowπ V (n + m) := by
  have h2 : (monoidalPowCat V m n).inv ≫ (β_ (monoidalPow V m) (monoidalPow V n)).hom ≫
      (monoidalPowCat V n m).hom ≫ eqToHom (congrArg (monoidalPow V) (Nat.add_comm n m)) ≫
        symPowπ V (m + n) = symPowπ V (m + n) := by
    have := (isTranspWord_monoidalPowBlockSwap V m n).comp_symPowπ
    simpa only [monoidalPowBlockSwap, Category.assoc] using this
  have h3 : (β_ (monoidalPow V m) (monoidalPow V n)).hom ≫ (monoidalPowCat V n m).hom ≫
      eqToHom (congrArg (monoidalPow V) (Nat.add_comm n m)) ≫ symPowπ V (m + n) =
        (monoidalPowCat V m n).hom ≫ symPowπ V (m + n) := by
    have := congrArg (fun t => (monoidalPowCat V m n).hom ≫ t) h2
    simpa only [Iso.hom_inv_id_assoc] using this
  rw [← symPowπ_comp_eqToHom V (Nat.add_comm n m)] at h3
  have h4 := congrArg (fun t => t ≫ eqToHom (congrArg (symPow V) (Nat.add_comm m n))) h3
  simp only [Category.assoc] at h4
  rw [symPowπ_comp_eqToHom V (Nat.add_comm m n), eqToHom_trans, eqToHom_refl, Category.comp_id] at h4
  exact h4

end AlgebraicGeometry.Scheme.Modules

/-- The left unit law. Route: cancel the quotient maps using that `symPowπ V 0 ⊗ symPowπ V m` is an epimorphism
(right exactness), reducing to the left unit law `monoidalPowCat_zero_left` of the tensor power multiplication. -/
theorem AlgebraicGeometry.Scheme.Modules.symPowMul_one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m : ℕ) :
    (CategoryTheory.MonoidalCategoryStruct.whiskerRight (X₁ := 𝟙_ X.Modules)
        (AlgebraicGeometry.Scheme.Modules.symPowπ V 0) (AlgebraicGeometry.Scheme.Modules.symPow V m)) ≫
        AlgebraicGeometry.Scheme.Modules.symPowMul V 0 m =
      (λ_ (AlgebraicGeometry.Scheme.Modules.symPow V m)).hom ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symPow V) (Nat.zero_add m).symm) := by
  open AlgebraicGeometry.Scheme.Modules in
  have := epi_whiskerLeft_of_epi (𝟙_ X.Modules) (symPowπ V m)
  exact aux_one_mul (symPowπ V 0) (symPowπ V m) (symPowMul V 0 m) (monoidalPowCat V 0 m).hom
    (symPowπ V (0 + m)) (tensorHom_symPowπ_symPowMul V 0 m) _
    (by rw [monoidalPowCat_zero_left, Category.assoc, ← symPowπ_comp_eqToHom V (Nat.zero_add m).symm])

/-- Associativity. Same route: the tensor product of the three quotient maps is an epimorphism, reducing to
the associativity of the tensor power multiplication. -/
theorem AlgebraicGeometry.Scheme.Modules.symPowMul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m n p : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.Modules.symPow V m) (AlgebraicGeometry.Scheme.Modules.symPow V n) (AlgebraicGeometry.Scheme.Modules.symPow V p)).hom ≫ (AlgebraicGeometry.Scheme.Modules.symPow V m ◁ AlgebraicGeometry.Scheme.Modules.symPowMul V n p) ≫ AlgebraicGeometry.Scheme.Modules.symPowMul V m (n + p) =
      (AlgebraicGeometry.Scheme.Modules.symPowMul V m n ▷ AlgebraicGeometry.Scheme.Modules.symPow V p) ≫ AlgebraicGeometry.Scheme.Modules.symPowMul V (m + n) p ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symPow V) (Nat.add_assoc m n p)) := by
  open AlgebraicGeometry.Scheme.Modules in
  have h1 := epi_tensorHom_of_epi (symPowπ V m) (symPowπ V n)
  have h2 := epi_tensorHom_of_epi (symPowπ V m ⊗ₘ symPowπ V n) (symPowπ V p)
  rw [← cancel_epi ((symPowπ V m ⊗ₘ symPowπ V n) ⊗ₘ symPowπ V p),
    MonoidalCategory.associator_naturality_assoc, MonoidalCategory.tensorHom_comp_whiskerLeft_assoc,
    tensorHom_symPowπ_symPowMul, ← MonoidalCategory.whiskerLeft_comp_tensorHom_assoc,
    tensorHom_symPowπ_symPowMul, MonoidalCategory.tensorHom_comp_whiskerRight_assoc,
    tensorHom_symPowπ_symPowMul, ← MonoidalCategory.whiskerRight_comp_tensorHom_assoc,
    tensorHom_symPowπ_symPowMul_assoc, symPowπ_comp_eqToHom V (Nat.add_assoc m n p),
    monoidalPowCat_assoc_assoc]

/-- Commutativity. Route: after reducing to tensor powers, the two sides differ by the `(m, n)`-block swap
permutation, and `symPowπ` is by definition invariant under permutations. -/
theorem AlgebraicGeometry.Scheme.Modules.symPowMul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (m n : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.Modules.symPow V m) (AlgebraicGeometry.Scheme.Modules.symPow V n)).hom ≫ AlgebraicGeometry.Scheme.Modules.symPowMul V n m =
      AlgebraicGeometry.Scheme.Modules.symPowMul V m n ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symPow V) (Nat.add_comm m n)) := by
  open AlgebraicGeometry.Scheme.Modules in
  have h1 := epi_tensorHom_of_epi (symPowπ V m) (symPowπ V n)
  rw [← cancel_epi (symPowπ V m ⊗ₘ symPowπ V n), BraidedCategory.braiding_naturality_assoc,
    tensorHom_symPowπ_symPowMul, tensorHom_symPowπ_symPowMul_assoc,
    symPowπ_comp_eqToHom V (Nat.add_comm m n), braiding_monoidalPowCat_symPowπ]
/-- The symmetric algebra for quasi-coherent `V`: `part m = Sym^m V`, multiplication `symPowMul`, unit the
quotient map `𝟙_ = V^{⊗0} → Sym^0 V`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) (_hV : V.IsQuasicoherent) : X.GradedQCAlgebra where
  part m := AlgebraicGeometry.Scheme.Modules.symPow V m
  quasicoherent := AlgebraicGeometry.Scheme.Modules.symPow_isQuasicoherent V _hV
  mul m n := AlgebraicGeometry.Scheme.Modules.symPowMul V m n
  one := AlgebraicGeometry.Scheme.Modules.symPowπ V 0
  one_mul := AlgebraicGeometry.Scheme.Modules.symPowMul_one_mul V
  mul_assoc := AlgebraicGeometry.Scheme.Modules.symPowMul_assoc V
  mul_comm := AlgebraicGeometry.Scheme.Modules.symPowMul_comm V

/-- The graded pieces of the trivial graded algebra: `part 0 = O_X`, the others the zero sheaf. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart (X : AlgebraicGeometry.Scheme.{u}) :
    ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | _ + 1 => 0

/-- The multiplication of the trivial graded algebra: `O_X ⊗ O_X → O_X` is the left unitor, the rest is zero. -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul (X : AlgebraicGeometry.Scheme.{u}) :
    ∀ m n, AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m ⊗
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X n ⟶
      AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X (m + n)
  | 0, 0 => (λ_ (𝟙_ X.Modules)).hom
  | _, _ => 0

/- The four proof obligations of `GradedQCAlgebra.trivial`. -/

/-- Quasi-coherence of the pieces: `m = 0` is `O_X`, `m ≥ 1` is the zero sheaf. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart_isQuasicoherent
    (X : AlgebraicGeometry.Scheme.{u}) (m : ℕ) :
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m).IsQuasicoherent := by
  cases m with
  | zero => exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorUnit X
  | succ m => exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_zero X

/-- Left unit law: for `m = 0` both sides are `λ_`; for `m ≥ 1` the source `𝟙_ ⊗ 0` is a zero object. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_one_mul
    (X : AlgebraicGeometry.Scheme.{u}) (m : ℕ) :
    ((𝟙 (𝟙_ X.Modules) : 𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X 0) ▷
          AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X 0 m =
      (λ_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m)).hom ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.zero_add m).symm) := by
  cases m with
  | zero =>
    have e : eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.zero_add 0).symm) =
      𝟙 (𝟙_ X.Modules) := rfl
    show (𝟙 (𝟙_ X.Modules) ▷ 𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom = (λ_ (𝟙_ X.Modules)).hom ≫ _
    rw [e, MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id]
  | succ m => exact (CategoryTheory.Limits.isZero_zero X.Modules).eq_of_tgt _ _

/-- Associativity: for `m = n = p = 0` this is the coherence of `λ_` in a monoidal category (`unitors_equal` +
the triangle); otherwise some factor is a zero object. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_assoc
    (X : AlgebraicGeometry.Scheme.{u}) (m n p : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m)
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X n)
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X p)).hom ≫
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m ◁
          AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X n p) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X m (n + p) =
      (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X m n ▷
          AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X p) ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X (m + n) p ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.add_assoc m n p)) := by
  rcases m with _ | m <;> rcases n with _ | n <;> rcases p with _ | p
  · have e : eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.add_assoc 0 0 0)) =
      𝟙 (𝟙_ X.Modules) := rfl
    show (α_ (𝟙_ X.Modules) (𝟙_ X.Modules) (𝟙_ X.Modules)).hom ≫ (𝟙_ X.Modules ◁ (λ_ (𝟙_ X.Modules)).hom) ≫
        (λ_ (𝟙_ X.Modules)).hom =
      ((λ_ (𝟙_ X.Modules)).hom ▷ 𝟙_ X.Modules) ≫ (λ_ (𝟙_ X.Modules)).hom ≫ _
    rw [e, Category.comp_id]
    monoidal
  all_goals exact (CategoryTheory.Limits.isZero_zero X.Modules).eq_of_tgt _ _

/-- Commutativity: for `m = n = 0` this is `β_{𝟙,𝟙} ≫ λ_ = λ_` (`braiding_leftUnitor` + `unitors_equal`);
otherwise zero. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_comm
    (X : AlgebraicGeometry.Scheme.{u}) (m n : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X m)
          (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X n)).hom ≫
        AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X n m =
      AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X m n ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.add_comm m n)) := by
  rcases m with _ | m <;> rcases n with _ | n
  · have e : eqToHom (congrArg (AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X) (Nat.add_comm 0 0)) =
      𝟙 (𝟙_ X.Modules) := rfl
    show (β_ (𝟙_ X.Modules) (𝟙_ X.Modules)).hom ≫ (λ_ (𝟙_ X.Modules)).hom = (λ_ (𝟙_ X.Modules)).hom ≫ _
    rw [e, Category.comp_id, braiding_leftUnitor, MonoidalCategory.unitors_equal]
  all_goals exact (CategoryTheory.Limits.isZero_zero X.Modules).eq_of_tgt _ _

/-- The trivial graded algebra: `part 0 = O_X`, the others the zero sheaf; the multiplication `O_X ⊗ O_X → O_X`
is the left unitor, the rest is zero (the fallback branch of `symGradedAlgebra`). -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial (X : AlgebraicGeometry.Scheme.{u}) :
    X.GradedQCAlgebra where
  part := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart X
  quasicoherent := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialPart_isQuasicoherent X
  mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul X
  one := 𝟙 _
  one_mul := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_one_mul X
  mul_assoc := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_assoc X
  mul_comm := AlgebraicGeometry.Scheme.GradedQCAlgebra.trivialMul_comm X

/-- `Sym(V)`: for quasi-coherent `V` the construction above, otherwise the trivial graded algebra (the paper only
uses it for quasi-coherent `V`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.symGradedAlgebra {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : X.GradedQCAlgebra :=
  @dite _ V.IsQuasicoherent (Classical.propDecidable _)
    (fun h => AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC V h)
    (fun _ => AlgebraicGeometry.Scheme.GradedQCAlgebra.trivial X)

end
