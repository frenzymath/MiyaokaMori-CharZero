import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesIsoTransport
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorLineBundleExact
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks08aa
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorAssociator
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorUnit

/-! # Iterated twists by a list of line bundles

Iterated twist `G ⊗ 𝓜 i₁ ⊗ ⋯ ⊗ 𝓜 iₘ` of a module sheaf by a list of line bundles, and its formal
properties used in the proof of Snapper's theorem (Stacks 0BEM):

* `twistList 𝓜 l G := l.foldl (fun G i => G.tensor (𝓜 i)) G`; the statement of 0BEM is
  `twistList (fun i => L i ^ n i) (List.finRange r) F` (definitionally).
* functoriality in `G` (`twistList_mapIso`), compatibility with tensoring on the left / right
  (`twistList_tensor_iso`, `twistList_tensor_right_iso`), with pushforward along a morphism via the
  projection formula (`twistList_pushforward_iso`), preservation of line bundles and of coherence,
  preservation of short exact sequences (`twistList_shortExact`) and hence additivity of `χ` on
  twisted short exact sequences (`sheafEulerCharacteristic_twistList_shortExact`), and the
  "raise one exponent" isomorphism (`twistList_update_iso`).

Everything here is formal (associativity / commutativity / unit isomorphisms of the tensor product,
exactness of `− ⊗ L` for a line bundle `L` (`TensorLineBundleExact`), the projection formula
(`ProjectionFormulaClosedImmersion`), additivity of `χ` (Stacks 08AA)).

Source: Stacks 0BEM (proof).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `twistList 𝓜 l G = G ⊗ 𝓜 i₁ ⊗ ⋯ ⊗ 𝓜 iₘ` for `l = [i₁, …, iₘ]` (left-nested, via `Modules.tensor`). -/
def twistList {r : ℕ} (𝓜 : Fin r → X.Modules) (l : List (Fin r)) (G : X.Modules) : X.Modules :=
  l.foldl (fun G i => G.tensor (𝓜 i)) G

@[simp] theorem twistList_nil {r : ℕ} (𝓜 : Fin r → X.Modules) (G : X.Modules) :
    twistList 𝓜 [] G = G := rfl

@[simp] theorem twistList_cons {r : ℕ} (𝓜 : Fin r → X.Modules) (i : Fin r) (l : List (Fin r))
    (G : X.Modules) : twistList 𝓜 (i :: l) G = twistList 𝓜 l (G.tensor (𝓜 i)) := rfl

theorem twistList_append {r : ℕ} (𝓜 : Fin r → X.Modules) (l₁ l₂ : List (Fin r)) (G : X.Modules) :
    twistList 𝓜 (l₁ ++ l₂) G = twistList 𝓜 l₂ (twistList 𝓜 l₁ G) :=
  List.foldl_append

/-- The 0BEM statement's `foldl` is a `twistList`. -/
theorem twistList_eq_foldl {r : ℕ} (L : Fin r → X.Modules) (n : Fin r → ℤ) (F : X.Modules) :
    (List.finRange r).foldl (fun (G : X.Modules) (i : Fin r) => G.tensor (L i ^ n i)) F
      = twistList (fun i => L i ^ n i) (List.finRange r) F := rfl

/-- If two families agree on the members of `l`, the twists agree. -/
theorem twistList_congr {r : ℕ} {𝓜 𝓝 : Fin r → X.Modules} (l : List (Fin r))
    (h : ∀ i ∈ l, 𝓜 i = 𝓝 i) (G : X.Modules) : twistList 𝓜 l G = twistList 𝓝 l G := by
  induction l generalizing G with
  | nil => rfl
  | cons i l ih =>
    rw [twistList_cons, twistList_cons, h i (List.mem_cons_self ..)]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

/-- Functoriality of the twist in the sheaf being twisted (on isomorphisms). -/
def twistList_mapIso {r : ℕ} (𝓜 : Fin r → X.Modules) (l : List (Fin r)) {G G' : X.Modules}
    (e : G ≅ G') : twistList 𝓜 l G ≅ twistList 𝓜 l G' :=
  match l with
  | [] => e
  | i :: l => twistList_mapIso 𝓜 l (tensorIsoLeft e (𝓜 i))

/-- Associativity of `Modules.tensor`, written for `Scheme.Modules.tensor`. -/
def twistTensorAssocIso (A B C : X.Modules) : (A.tensor B).tensor C ≅ A.tensor (B.tensor C) :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorAssociator A B C

/-- `(G ⊗ M) ⊗ N ≅ (G ⊗ N) ⊗ M`. -/
def tensorRightSwapIso (G M N : X.Modules) : (G.tensor M).tensor N ≅ (G.tensor N).tensor M :=
  twistTensorAssocIso G M N ≪≫ tensorIsoRight G (tensorSymmIso M N) ≪≫ (twistTensorAssocIso G N M).symm

/-- Twisting `A ⊗ B` twists the right factor: `(A ⊗ B) ⊗ 𝓜_l ≅ A ⊗ (B ⊗ 𝓜_l)`. -/
def twistList_tensor_iso {r : ℕ} (𝓜 : Fin r → X.Modules) (l : List (Fin r)) (A B : X.Modules) :
    twistList 𝓜 l (A.tensor B) ≅ A.tensor (twistList 𝓜 l B) :=
  match l with
  | [] => Iso.refl _
  | i :: l =>
    twistList_mapIso 𝓜 l (twistTensorAssocIso A B (𝓜 i)) ≪≫ twistList_tensor_iso 𝓜 l A (B.tensor (𝓜 i))

/-- An extra factor commutes past the twist: `(G ⊗ M) ⊗ 𝓜_l ≅ (G ⊗ 𝓜_l) ⊗ M`. -/
def twistList_tensor_right_iso {r : ℕ} (𝓜 : Fin r → X.Modules) (l : List (Fin r))
    (G M : X.Modules) : twistList 𝓜 l (G.tensor M) ≅ (twistList 𝓜 l G).tensor M :=
  match l with
  | [] => Iso.refl _
  | i :: l =>
    twistList_mapIso 𝓜 l (tensorRightSwapIso G M (𝓜 i)) ≪≫
      twistList_tensor_right_iso 𝓜 l (G.tensor (𝓜 i)) M

/-- `G ⊗ 𝓜_l ≅ G ⊗ (O_X ⊗ 𝓜_l)`: the twist is tensoring with the single line bundle `O_X ⊗ 𝓜_l`. -/
def twistList_iso_tensor_unit {r : ℕ} (𝓜 : Fin r → X.Modules) (l : List (Fin r)) (G : X.Modules) :
    twistList 𝓜 l G ≅ G.tensor (twistList 𝓜 l (SheafOfModules.unit X.ringCatSheaf)) :=
  twistList_mapIso 𝓜 l (AlgebraicGeometry.Scheme.Modules.moduleTensorRightUnitIso G).symm ≪≫
    twistList_tensor_iso 𝓜 l G (SheafOfModules.unit X.ringCatSheaf)

/-- Twisting a line bundle by line bundles gives a line bundle. -/
theorem twistList_isLineBundle {r : ℕ} (𝓜 : Fin r → X.Modules) [∀ i, (𝓜 i).IsLineBundle]
    (l : List (Fin r)) (G : X.Modules) [G.IsLineBundle] : (twistList 𝓜 l G).IsLineBundle := by
  induction l generalizing G with
  | nil => exact inferInstanceAs G.IsLineBundle
  | cons i l ih =>
    rw [twistList_cons]
    exact ih (G.tensor (𝓜 i))

/-- Coherent `⊗` line bundle is coherent (quasi-coherence: Stacks 01CE; finite type: 01B6-style). -/
theorem isCoherent_tensor_of_isLineBundle (G M : X.Modules) [G.IsCoherent] [M.IsLineBundle] :
    (G.tensor M).IsCoherent := by
  have hq : G.IsQuasicoherent := IsCoherent.quasicoherent
  have hf : G.IsFiniteType := IsCoherent.finiteType
  exact ⟨inferInstance, inferInstance⟩

/-- Twisting a coherent sheaf by line bundles gives a coherent sheaf. -/
theorem twistList_isCoherent {r : ℕ} (𝓜 : Fin r → X.Modules) [∀ i, (𝓜 i).IsLineBundle]
    (l : List (Fin r)) (G : X.Modules) [G.IsCoherent] : (twistList 𝓜 l G).IsCoherent := by
  induction l generalizing G with
  | nil => exact inferInstanceAs G.IsCoherent
  | cons i l ih =>
    rw [twistList_cons]
    have := isCoherent_tensor_of_isLineBundle G (𝓜 i)
    exact ih (G.tensor (𝓜 i))

/-- Coherence is invariant under isomorphism. -/
theorem isCoherent_of_iso {M N : X.Modules} (e : M ≅ N) [hM : M.IsCoherent] : N.IsCoherent :=
  ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e hM.quasicoherent,
    isFiniteType_of_iso e hM.finiteType⟩

/-- Twisting by line bundles preserves short exact sequences (iterate `shortExact_tensor_lineBundle`). -/
theorem twistList_shortExact {r : ℕ} (𝓜 : Fin r → X.Modules) [∀ i, (𝓜 i).IsLineBundle]
    (l : List (Fin r)) (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact) :
    ∃ (T : CategoryTheory.ShortComplex X.Modules) (_ : T.X₁ ≅ twistList 𝓜 l S.X₁)
      (_ : T.X₂ ≅ twistList 𝓜 l S.X₂) (_ : T.X₃ ≅ twistList 𝓜 l S.X₃), T.ShortExact := by
  induction l generalizing S with
  | nil => exact ⟨S, Iso.refl _, Iso.refl _, Iso.refl _, hS⟩
  | cons i l ih =>
    obtain ⟨T', e₁, e₂, e₃, -, -, hT'⟩ := shortExact_tensor_lineBundle (𝓜 i) S hS
    obtain ⟨T, f₁, f₂, f₃, hT⟩ := ih T' hT'
    refine ⟨T, f₁ ≪≫ twistList_mapIso 𝓜 l (e₁ ≪≫ (tensorIsoTensorObj _ _).symm),
      f₂ ≪≫ twistList_mapIso 𝓜 l (e₂ ≪≫ (tensorIsoTensorObj _ _).symm),
      f₃ ≪≫ twistList_mapIso 𝓜 l (e₃ ≪≫ (tensorIsoTensorObj _ _).symm), hT⟩

/-- Additivity of `χ` on a twisted short exact sequence (Stacks 08AA after `twistList_shortExact`). -/
theorem sheafEulerCharacteristic_twistList_shortExact {k : Type u} [Field k]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    {r : ℕ} (𝓜 : Fin r → X.Modules) [∀ i, (𝓜 i).IsLineBundle] (l : List (Fin r))
    (S : CategoryTheory.ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (twistList 𝓜 l S.X₂) =
      AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (twistList 𝓜 l S.X₁) +
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (twistList 𝓜 l S.X₃) := by
  obtain ⟨T, e₁, e₂, e₃, hT⟩ := twistList_shortExact 𝓜 l S hS
  have h1 : (twistList 𝓜 l S.X₁).IsCoherent := twistList_isCoherent 𝓜 l S.X₁
  have h2 : (twistList 𝓜 l S.X₂).IsCoherent := twistList_isCoherent 𝓜 l S.X₂
  have h3 : (twistList 𝓜 l S.X₃).IsCoherent := twistList_isCoherent 𝓜 l S.X₃
  have c1 : T.X₁.IsCoherent := isCoherent_of_iso e₁.symm
  have c2 : T.X₂.IsCoherent := isCoherent_of_iso e₂.symm
  have c3 : T.X₃.IsCoherent := isCoherent_of_iso e₃.symm
  have hadd := AlgebraicGeometry.sheafEulerCharacteristic_additive (k := k) X hX T hT
  rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₁,
    AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₂,
    AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₃] at hadd
  exact hadd

/-- Twisting a pushforward: `i_*G ⊗ 𝓜_l ≅ i_*(G ⊗ (i^*𝓜)_l)` (iterated projection formula,
holds for any morphism `i`). -/
def twistList_pushforward_iso {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) {r : ℕ}
    (𝓜 : Fin r → X.Modules) [∀ j, (𝓜 j).IsLineBundle] (l : List (Fin r)) (G : Z.Modules) :
    twistList 𝓜 l ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (twistList (fun j => (AlgebraicGeometry.Scheme.Modules.pullback i).obj (𝓜 j)) l G) :=
  match l with
  | [] => Iso.refl _
  | j :: l =>
    twistList_mapIso 𝓜 l (pushforwardTensorPullbackIso i G (𝓜 j)).symm ≪≫
      twistList_pushforward_iso i 𝓜 l (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (𝓜 j)))

/-- Raising one factor: if `𝓝` agrees with `𝓜` away from `j` and `𝓝 j ≅ 𝓜 j ⊗ M`, then for a list
`l₁ ++ j :: l₂` not containing `j` elsewhere, `G ⊗ 𝓝_l ≅ (G ⊗ 𝓜_l) ⊗ M`. -/
def twistList_update_iso {r : ℕ} {𝓜 𝓝 : Fin r → X.Modules} {j : Fin r} {M : X.Modules}
    (h : ∀ i, i ≠ j → 𝓝 i = 𝓜 i) (e : 𝓝 j ≅ (𝓜 j).tensor M) (l₁ l₂ : List (Fin r))
    (h₁ : j ∉ l₁) (h₂ : j ∉ l₂) (G : X.Modules) :
    twistList 𝓝 (l₁ ++ j :: l₂) G ≅ (twistList 𝓜 (l₁ ++ j :: l₂) G).tensor M := by
  have c₁ : twistList 𝓝 l₁ G = twistList 𝓜 l₁ G :=
    twistList_congr l₁ (fun i hi => h i (fun hij => h₁ (hij ▸ hi))) G
  have c₂ : ∀ H, twistList 𝓝 l₂ H = twistList 𝓜 l₂ H := fun H =>
    twistList_congr l₂ (fun i hi => h i (fun hij => h₂ (hij ▸ hi))) H
  rw [twistList_append, twistList_append, twistList_cons, twistList_cons, c₁, c₂]
  exact twistList_mapIso 𝓜 l₂ (tensorIsoRight _ e ≪≫ (twistTensorAssocIso _ _ _).symm) ≪≫
    twistList_tensor_right_iso 𝓜 l₂ _ M

/-- The `List.finRange r` version of `twistList_update_iso`. -/
theorem twistList_finRange_update_iso {r : ℕ} {𝓜 𝓝 : Fin r → X.Modules} {j : Fin r} {M : X.Modules}
    (h : ∀ i, i ≠ j → 𝓝 i = 𝓜 i) (e : 𝓝 j ≅ (𝓜 j).tensor M) (G : X.Modules) :
    Nonempty (twistList 𝓝 (List.finRange r) G ≅ (twistList 𝓜 (List.finRange r) G).tensor M) := by
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem (List.mem_finRange j)
  have hnd : (l₁ ++ j :: l₂).Nodup := hl ▸ List.nodup_finRange r
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd₂, hdisj⟩ := hnd
  have h₂ : j ∉ l₂ := (List.nodup_cons.mp hnd₂).1
  have h₁ : j ∉ l₁ := fun hj => hdisj j hj j (List.mem_cons_self ..) rfl
  rw [hl]
  exact ⟨twistList_update_iso h e l₁ l₂ h₁ h₂ G⟩

end AlgebraicGeometry.Scheme.Modules

end
