import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleForwardBackwardTransport

/-! # The section API for the inverse identities `α ≫ β = 𝟙` and `β ≫ α = 𝟙`

Definitions whose *types* are stated with nested pullbacks only (`pullbackSection`, `transportSection`,
`uncompSection`, `totalSpaceHomEquiv'`, `coordinateOf`, `contractSections'`), and the lemmas about them
(naturality, transport, extensionality, `contractSections_pullback`, the abstract core of α ≫ β = 𝟙).
Concrete proofs must use these and never spell out `pullbackComp`/`pullbackCongr`/`(Over.mk _).hom`
themselves; see the section docstring below.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## The section API: nested-form types only

Every function below is a plain definition whose *type* is stated with nested pullbacks
`(pullback f).obj M` (never `pullback g ⋙ pullback f`, `(Over.mk f).hom`, or `Γ(M, ⊤)`), while its body
is the usual `pullbackComp`/`pullbackCongr`/`totalSpaceHomEquiv`/`contractSections` term. Concrete proofs
combine these functions and the lemmas about them by `congrArg`/`Eq.trans` only, so that all
unifications are syntactic. Measured: a hand-written `((pullbackComp β g).hom.app _).val.app
(op ⊤)).hom (sectionPullbackAlong β x)` with concrete `g` costs 5–30 s per occurrence (Lean tries
`Modules.pullback g ≟ pullback g ⋙ pullback β` before reducing the functor projection). -/

namespace AlgebraicGeometry.Scheme.Modules

variable {S S' P C : AlgebraicGeometry.Scheme.{u}}

/-- Γ(S, f^*M) → Γ(S', (j ≫ f)^*M): pull back along `j`, identified through `pullbackComp j f`. -/
def pullbackSection (j : S' ⟶ S) (f : S ⟶ P) (M : P.Modules)
    (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullback (j ≫ f)).obj M).val.obj (Opposite.op ⊤) : Type u) :=
  (((pullbackComp j f).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong j x)

/-- Transport of a section along an equality `f = f'` of morphisms (`pullbackCongr`). -/
def transportSection {f f' : S ⟶ P} (h : f = f') (M : P.Modules)
    (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullback f').obj M).val.obj (Opposite.op ⊤) : Type u) :=
  (((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom x

/-- Γ(S, (g ≫ p)^*A) → Γ(S, g^*(p^*A)) (`(pullbackComp g p).inv`). -/
def uncompSection (g : S ⟶ P) (p : P ⟶ C) (A : C.Modules)
    (z : (((pullback (g ≫ p)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullback g).obj ((pullback p).obj A)).val.obj (Opposite.op ⊤) : Type u) :=
  (((pullbackComp g p).inv.app A).val.app (Opposite.op ⊤)).hom z

theorem transportSection_self {f : S ⟶ P} (h : f = f) (M : P.Modules)
    (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) : transportSection h M x = x := rfl

theorem transportSection_transportSection {f f' f'' : S ⟶ P} (h : f = f') (h' : f' = f'') (M : P.Modules)
    (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    transportSection h' M (transportSection h M x) = transportSection (h.trans h') M x := by
  subst h h'; rfl

theorem transportSection_sectionPullbackAlong {f f' : S ⟶ P} (h : f = f') (M : P.Modules)
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    transportSection h M (sectionPullbackAlong f s) = sectionPullbackAlong f' s := by
  subst h; rfl

/-- j^*(f^*s), transported along `j ≫ f = π`, is π^*s. -/
theorem transportSection_pullbackSection_sectionPullbackAlong (j : S' ⟶ S) (f : S ⟶ P) (π : S' ⟶ P)
    (h : j ≫ f = π) (M : P.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    transportSection h M (pullbackSection j f M (sectionPullbackAlong f s)) = sectionPullbackAlong π s := by
  subst h
  rw [transportSection_self]
  exact pullbackComp_hom_apply_sectionPullbackAlong_sectionPullbackAlong j f M s

/-- Bridge to the Contract's `.app ⊤` spelling (variable-level `rfl`; instantiate it syntactically). -/
theorem transportSection_pullbackSection_eq_app (j : S' ⟶ S) (f : S ⟶ P) (π : S' ⟶ P) (h : j ≫ f = π)
    (M : P.Modules) (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    transportSection h M (pullbackSection j f M x) =
      ((pullbackCongr h).hom.app M).app ⊤ (((pullbackComp j f).hom.app M).app ⊤ (sectionPullbackAlong j x)) :=
  rfl

/-- Bridge to the Contract's `.app ⊤` spelling for `coordOverProduct` (variable-level `rfl`). -/
theorem uncompSection_transportSection_eq_app (g : S ⟶ P) (p : P ⟶ C) (A : C.Modules) {t : S ⟶ C}
    (h : t = g ≫ p) (z : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    uncompSection g p A (transportSection h A z) =
      ((pullbackComp g p).inv.app A).app ⊤ (((pullbackCongr h).hom.app A).app ⊤ z) :=
  rfl

/-- Abstract core of α ≫ β = 𝟙 in the section API (see `coordinate_comp_eq_of_pullback_pullback_eq`). -/
theorem coordinate_comp_eq_of_pullback_pullback_eq' (p : P ⟶ C) (A : C.Modules)
    (g : S ⟶ P) (π : S' ⟶ P) (α : S ⟶ S') (β : S' ⟶ S) (hα1 : α ≫ π = g) (hβ1 : β ≫ g = π)
    (t : S ⟶ C) (ht : g ≫ p = t) (z : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (H : transportSection hα1 ((pullback p).obj A)
        (pullbackSection α π ((pullback p).obj A)
          (transportSection hβ1 ((pullback p).obj A)
            (pullbackSection β g ((pullback p).obj A) (uncompSection g p A (transportSection ht.symm A z))))) =
      uncompSection g p A (transportSection ht.symm A z))
    (hφ : (α ≫ β) ≫ t = t) :
    transportSection hφ A (pullbackSection (α ≫ β) t A z) = z :=
  coordinate_comp_eq_of_pullback_pullback_eq p A g π α β hα1 hβ1 t ht z H hφ

end AlgebraicGeometry.Scheme.Modules

/-- `totalSpaceHomEquiv` on `Over.mk f` and `Over.homMk a w`, typed through `f`. -/
def AlgebraicGeometry.Scheme.totalSpaceHomEquiv' {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {S : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ X)
    (a : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left) (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f) :
    (((AlgebraicGeometry.Scheme.Modules.pullback f).obj V).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk f) (CategoryTheory.Over.homMk a w)

theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_injective {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {S : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ X)
    (a₁ a₂ : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (w₁ : a₁ ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f)
    (w₂ : a₂ ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f)
    (h : AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V f a₁ w₁ = AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V f a₂ w₂) :
    a₁ = a₂ :=
  CategoryTheory.Over.left_eq_of_homMk_eq_mk w₁ w₂
    ((AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk f)).injective h)

/-- Transport along `f = f'`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_congr {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {S : AlgebraicGeometry.Scheme.{u}} {f f' : S ⟶ X} (h : f = f')
    (a : S ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left)
    (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f) (w' : a ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f') :
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V f' a w' =
      AlgebraicGeometry.Scheme.Modules.transportSection h V (AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V f a w) := by
  subst h; rfl

/-- Naturality (`totalSpaceHomEquiv_naturality`) in the section API. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv'_comp {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (j : S ⟶ T)
    (a : T ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left) (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = f)
    (w' : (j ≫ a) ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom = j ≫ f) :
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V (j ≫ f) (j ≫ a) w' =
      AlgebraicGeometry.Scheme.Modules.pullbackSection j f V (AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V f a w) :=
  AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality V (CategoryTheory.Over.mk f) j (CategoryTheory.Over.homMk a w)

/-- `tautologicalSection` in the section API. -/
theorem AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection_eq' {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.Scheme.totalSpacePunctured.tautologicalSection V =
      AlgebraicGeometry.Scheme.totalSpaceHomEquiv' V (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase V)
        (AlgebraicGeometry.Scheme.totalSpacePunctured V).ι
        (AlgebraicGeometry.Scheme.totalSpacePunctured.toBase_eq V).symm := rfl

/-- The ℓ-th coordinate of the morphism `Over.homMk a w : Over.mk f ⟶ Tot(A^{⊕n})`, typed through `f`. -/
def AlgebraicGeometry.Scheme.coordinateOf {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.Modules) [A.IsLocallyFree] [A.IsFiniteType] (n : ℕ) {S : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ X)
    (a : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left)
    (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f) (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullback f).obj A).val.obj (Opposite.op ⊤) : Type u) :=
  (((AlgebraicGeometry.Scheme.Modules.pullback f).map (biproduct.π (fun _ : Fin n => A) ℓ)).val.app (Opposite.op ⊤)).hom
    (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A n) (CategoryTheory.Over.mk f)
      (CategoryTheory.Over.homMk a w))

theorem AlgebraicGeometry.Scheme.coordinateOf_congr {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.Modules) [A.IsLocallyFree] [A.IsFiniteType] (n : ℕ) {S : AlgebraicGeometry.Scheme.{u}} {f f' : S ⟶ X}
    (h : f = f') (a : S ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left)
    (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f)
    (w' : a ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f') (ℓ : Fin n) :
    AlgebraicGeometry.Scheme.coordinateOf A n f' a w' ℓ =
      AlgebraicGeometry.Scheme.Modules.transportSection h A (AlgebraicGeometry.Scheme.coordinateOf A n f a w ℓ) := by
  subst h; rfl

/-- `totalSpaceHomEquiv_naturality_coordinate` in the section API. -/
theorem AlgebraicGeometry.Scheme.coordinateOf_comp {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.Modules) [A.IsLocallyFree] [A.IsFiniteType] (n : ℕ) {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (j : S ⟶ T)
    (a : T ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left)
    (w : a ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f)
    (w' : (j ≫ a) ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = j ≫ f) (ℓ : Fin n) :
    AlgebraicGeometry.Scheme.coordinateOf A n (j ≫ f) (j ≫ a) w' ℓ =
      AlgebraicGeometry.Scheme.Modules.pullbackSection j f A (AlgebraicGeometry.Scheme.coordinateOf A n f a w ℓ) :=
  AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate (fun _ : Fin n => A) (CategoryTheory.Over.mk f) j
    (CategoryTheory.Over.homMk a w) ℓ

/-- `totalSpaceHom_ext_of_coordinates` in the section API. -/
theorem AlgebraicGeometry.Scheme.ext_of_coordinateOf {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.Modules) [A.IsLocallyFree] [A.IsFiniteType] (n : ℕ) {T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X)
    (a₁ a₂ : T ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left)
    (w₁ : a₁ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f)
    (w₂ : a₂ ≫ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom = f)
    (h : ∀ ℓ : Fin n, AlgebraicGeometry.Scheme.coordinateOf A n f a₁ w₁ ℓ = AlgebraicGeometry.Scheme.coordinateOf A n f a₂ w₂ ℓ) :
    a₁ = a₂ :=
  CategoryTheory.Over.left_eq_of_homMk_eq_mk w₁ w₂
    (AlgebraicGeometry.Scheme.totalSpaceHom_ext_of_coordinates (fun _ : Fin n => A) (CategoryTheory.Over.mk f) _ _ h)

/-- `contractSections` on `Over.mk f`, typed through `f`. -/
def conePuncturedLineBundle.contractSections' {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] {S : AlgebraicGeometry.Scheme.{u}}
    (f : S ⟶ CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (w : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (conePuncturedLineBundle e A)).val.obj (Opposite.op ⊤) : Type u)) (q : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A)).val.obj (Opposite.op ⊤) : Type u) :=
  conePuncturedLineBundle.contractSections e A (CategoryTheory.Over.mk f) w q

theorem conePuncturedLineBundle.contractSections'_eq {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] {S : AlgebraicGeometry.Scheme.{u}}
    (f : S ⟶ CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (w : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (conePuncturedLineBundle e A)).val.obj (Opposite.op ⊤) : Type u)) (q : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    conePuncturedLineBundle.contractSections' e A f w q =
      conePuncturedLineBundle.contractSections e A (CategoryTheory.Over.mk f) w q := rfl

/-- Transport of the pairing along `f = f'`. -/
theorem conePuncturedLineBundle.contractSections'_congr {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] {S : AlgebraicGeometry.Scheme.{u}}
    {f f' : S ⟶ CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))} (h : f = f') (w : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (conePuncturedLineBundle e A)).val.obj (Opposite.op ⊤) : Type u)) (q : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    conePuncturedLineBundle.contractSections' e A f' (AlgebraicGeometry.Scheme.Modules.transportSection h _ w)
        (AlgebraicGeometry.Scheme.Modules.transportSection h _ q) =
      AlgebraicGeometry.Scheme.Modules.transportSection h _ (conePuncturedLineBundle.contractSections' e A f w q) := by
  subst h; rfl

/-- `contractSections_pullback` in the section API. -/
theorem conePuncturedLineBundle.contractSections'_pullback {k : Type u} [Field k]
    {C X : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle] {T S : AlgebraicGeometry.Scheme.{u}}
    (f : T ⟶ CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) (j : S ⟶ T) (w : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (conePuncturedLineBundle e A)).val.obj (Opposite.op ⊤) : Type u)) (q : (((AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSection j f _ (conePuncturedLineBundle.contractSections' e A f w q) =
      conePuncturedLineBundle.contractSections' e A (j ≫ f) (AlgebraicGeometry.Scheme.Modules.pullbackSection j f _ w)
        (AlgebraicGeometry.Scheme.Modules.pullbackSection j f _ q) := by
  have h := conePuncturedLineBundle.contractSections_pullback e A (CategoryTheory.Over.mk f) j w q
  simp only [AlgebraicGeometry.Scheme.Modules.hom_app_top_eq] at h
  exact h

/-- `coord` in the section API (`toTot` written out as `Over.homMk`). -/
theorem puncturedConeToProduct.coord_eq' {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N δ : ℕ}
    (e : ProjectiveEmbedding k X N) (E : EmbeddingEquations k e δ) (A : C.Modules) [A.IsLineBundle]
    (hdeg : ∀ j, 0 < E.deg j) (ℓ : Fin (N + 1)) :
    puncturedConeToProduct.coord e E A hdeg ℓ =
      AlgebraicGeometry.Scheme.coordinateOf A (N + 1) (puncturedConeToProduct.base e E A hdeg)
        ((puncturedCone A N E.deg hdeg E.F E.homogeneous).ι ≫
          (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
            (homogeneousEquationSection A N (E.F j) (E.homogeneous j))).subschemeι)
        (puncturedConeToProduct.toTot_w e E A hdeg) ℓ := rfl

end
