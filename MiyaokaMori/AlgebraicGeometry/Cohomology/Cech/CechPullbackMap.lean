import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAltFunctorial
import MiyaokaMori.CategoryTheory.AdjointComplexIso

/-! # The pullback map on Čech complexes

Let `g : Y → X` be a morphism of schemes, `φ : A → A'` a ring homomorphism, and `a : A → Γ(X, O_X)`,
`a' : A' → Γ(Y, O_Y)` with `g^♯ ∘ a = a' ∘ φ`. For a family of opens `U` of `X` and an `O_X`-module
`M`, pullback of sections `s ↦ (g^*s)|_{V'}` (`V' ⊆ g⁻¹V`) gives `A`-linear maps
`Γ(M, V) → Γ(g^*M, V')` (`pullbackSectionsLinear`), which assemble termwise into a chain map of
complexes of `A`-modules `cechPullbackMap : Č(U, M)_A ⟶ (Č(g⁻¹U, g^*M)_{A'})_A`.

Source: Stacks 01XL/01XM and the second paragraph of the proof of 02KH ("the Čech complex of the
pullback is the base change of the Čech complex"); the proof of Hartshorne III.9.3 (p. 255).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)

/-- Functoriality of restriction maps (elementwise). -/
theorem famRes_comp' {Z : AlgebraicGeometry.Scheme.{u}} (N : Z.Modules) {u₁ u₂ u₃ : Z.Opens}
    (h : u₂ ≤ u₁) (h' : u₃ ≤ u₂) (x : Γ(N, u₁)) :
    N.presheaf.map (homOfLE h').op (N.presheaf.map (homOfLE h).op x) =
      N.presheaf.map (homOfLE (h'.trans h)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The unit of the pullback–pushforward adjunction on `V`: `Γ(M, V) → Γ(g^*M, g⁻¹V)` (additive). -/
def pullbackUnitHom (M : X.Modules) (V : X.Opens) :
    Γ(M, V) →+ Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ V) :=
  (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app V).hom

/-- The unit commutes with restriction. -/
theorem pullbackUnitHom_restrict (M : X.Modules) {V W : X.Opens} (hW : W ≤ V) (s : Γ(M, V)) :
    pullbackUnitHom g M W (M.presheaf.map (homOfLE hW).op s) =
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.map
        (homOfLE (show g ⁻¹ᵁ W ≤ g ⁻¹ᵁ V from fun _ hx => hW hx)).op (pullbackUnitHom g M V s) :=
  app_map ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) hW s

/-- Pullback of sections followed by restriction: `Γ(M, V) → Γ(g^*M, V')`, `V' ⊆ g⁻¹V`. -/
def pullbackSectionsOn (M : X.Modules) (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V) :
    Γ(M, V) →+ Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, V') :=
  (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE h).op).hom.comp
    (pullbackUnitHom g M V)

theorem pullbackSectionsOn_apply (M : X.Modules) (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V)
    (s : Γ(M, V)) :
    pullbackSectionsOn g M V V' h s =
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE h).op
        (pullbackUnitHom g M V s) := rfl

/-- Pullback commutes with restriction. -/
theorem pullbackSectionsOn_restrict (M : X.Modules) {V W : X.Opens} {V' W' : Y.Opens}
    (h : V' ≤ g ⁻¹ᵁ V) (h' : W' ≤ g ⁻¹ᵁ W) (hW : W ≤ V) (hW' : W' ≤ V') (s : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hW').op
        (pullbackSectionsOn g M V V' h s) =
      pullbackSectionsOn g M W W' h' (M.presheaf.map (homOfLE hW).op s) := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, pullbackUnitHom_restrict,
    famRes_comp', famRes_comp']

section Linear

variable {A A' : Type u} [CommRing A] [CommRing A'] (a : A →+* Γ(X, ⊤)) (a' : A' →+* Γ(Y, ⊤))
  (φ : A →+* A')

/-- Semilinearity of the unit: `η(x • s) = g^♯(x) • η(s)`. -/
theorem pullbackUnitHom_smul (M : X.Modules) (V : X.Opens) (x : Γ(X, V)) (s : Γ(M, V)) :
    pullbackUnitHom g M V (x • s) = (g.app V x) • pullbackUnitHom g M V s :=
  Hom.app_smul ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) x s

/-- Pullback of sections is semilinear for the `A`-action (`A` acts via `a`, `A'` via `a'`, and
`g^♯ ∘ a = a' ∘ φ`). -/
theorem pullbackSectionsOn_smul (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules)
    (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V) (r : A) (s : Γ(M, V)) :
    pullbackSectionsOn g M V V' h (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a r) • s) =
      Y.presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (a' (φ r)) • pullbackSectionsOn g M V V' h s := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, pullbackUnitHom_smul,
    AlgebraicGeometry.Scheme.Modules.map_smul]
  congr 1
  have h1 : a' (φ r) = g.appTop.hom (a r) := (RingHom.congr_fun hcomm r).symm
  rw [h1]
  have nat := ConcreteCategory.congr_hom (g.naturality (homOfLE (le_top : V ≤ ⊤)).op) (a r)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at nat
  rw [nat, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Preimages commute with finite intersections. -/
theorem preimage_iInf_eq {m : ℕ} (W : Fin m → X.Opens) :
    g ⁻¹ᵁ (⨅ k, W k) = ⨅ k, g ⁻¹ᵁ W k := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iInf]
  show g.base ⁻¹' ((⨅ k, W k : X.Opens) : Set X) = _
  rw [TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]
  rfl

/-- Pullback of sections as an `A`-linear map `Γ(M, V)_A → (Γ(g^*M, V')_{A'})_A`. -/
def pullbackSectionsLinear (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules)
    (V : X.Opens) (V' : Y.Opens) (h : V' ≤ g ⁻¹ᵁ V) :
    (ModuleCat.restrictScalars a).obj (M.sectionsOverTop V) ⟶
      (ModuleCat.restrictScalars φ).obj ((ModuleCat.restrictScalars a').obj
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop V')) :=
  ModuleCat.ofHom
    (X := ((ModuleCat.restrictScalars a).obj (M.sectionsOverTop V) : ModuleCat A))
    (Y := ((ModuleCat.restrictScalars φ).obj ((ModuleCat.restrictScalars a').obj
        (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop V')) : ModuleCat A))
    { toFun := pullbackSectionsOn g M V V' h
      map_add' := map_add _
      map_smul' := fun r s => pullbackSectionsOn_smul g a a' φ hcomm M V V' h r s }

variable {n : ℕ} (U : Fin n → X.Opens)

/-- Termwise: `Č^p(U, M)_A → (Č^p(g⁻¹U, g^*M)_{A'})_A`, with components `pullbackSectionsLinear`. -/
def cechPullbackTerm (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules) (p : ℕ) :
    (ModuleCat.restrictScalars a).obj (cechTermAlt U M p) ⟶
      (ModuleCat.restrictScalars φ).obj ((ModuleCat.restrictScalars a').obj
        (cechTermAlt (fun i => g ⁻¹ᵁ U i) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) p)) :=
  AdjointComplexIso.liftThrough (ModuleCat.restrictScalars a' ⋙ ModuleCat.restrictScalars φ)
    (fun σ : Fin (p + 1) ↪o Fin n =>
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop (⨅ k, g ⁻¹ᵁ U (σ k)))
    (fun σ => (ModuleCat.restrictScalars a).map
        (Pi.π (fun σ : Fin (p + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k))) σ) ≫
      pullbackSectionsLinear g a a' φ hcomm M (⨅ k, U (σ k)) (⨅ k, g ⁻¹ᵁ U (σ k))
        (le_of_eq (preimage_iInf_eq g fun k => U (σ k)).symm))

/-- `pullbackSectionsLinear` commutes with restriction maps. -/
theorem pullbackSectionsLinear_restrict (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules)
    {V W : X.Opens} {V' W' : Y.Opens} (h : V' ≤ g ⁻¹ᵁ V) (h' : W' ≤ g ⁻¹ᵁ W) (hW : W ≤ V)
    (hW' : W' ≤ V') :
    (ModuleCat.restrictScalars a).map (M.sectionsOverTopRestrict hW) ≫
        pullbackSectionsLinear g a a' φ hcomm M W W' h' =
      pullbackSectionsLinear g a a' φ hcomm M V V' h ≫
        (ModuleCat.restrictScalars a' ⋙ ModuleCat.restrictScalars φ).map
          (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTopRestrict hW') := by
  ext s
  exact (pullbackSectionsOn_restrict g M h h' hW hW' s).symm

theorem cechPullbackTerm_comm (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules) (p : ℕ) :
    cechPullbackTerm g a a' φ U hcomm M p ≫
        (ModuleCat.restrictScalars a' ⋙ ModuleCat.restrictScalars φ).map
          (cechDiffAlt (fun i => g ⁻¹ᵁ U i) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) p) =
      (ModuleCat.restrictScalars a).map (cechDiffAlt U M p) ≫
        cechPullbackTerm g a a' φ U hcomm M (p + 1) :=
  AdjointComplexIso.liftThrough_comm_of_components
    (ModuleCat.restrictScalars a' ⋙ ModuleCat.restrictScalars φ)
    (fun σ : Fin (p + 1) ↪o Fin n =>
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop (⨅ k, g ⁻¹ᵁ U (σ k)))
    (fun τ : Fin (p + 2) ↪o Fin n =>
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTop (⨅ k, g ⁻¹ᵁ U (τ k)))
    (ModuleCat.restrictScalars a)
    (fun σ : Fin (p + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k)))
    (fun τ : Fin (p + 2) ↪o Fin n => M.sectionsOverTop (⨅ k, U (τ k)))
    (fun (τ : Fin (p + 2) ↪o Fin n) k => (Fin.succAboveOrderEmb k).trans τ)
    (fun k => (-1 : ℤ) ^ (k : ℕ))
    (fun τ k => M.sectionsOverTopRestrict (cech_face_le U τ k))
    (fun τ k => ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).sectionsOverTopRestrict
      (cech_face_le (fun i => g ⁻¹ᵁ U i) τ k))
    (fun σ => pullbackSectionsLinear g a a' φ hcomm M (⨅ k, U (σ k)) (⨅ k, g ⁻¹ᵁ U (σ k))
      (le_of_eq (preimage_iInf_eq g fun k => U (σ k)).symm))
    (fun τ => pullbackSectionsLinear g a a' φ hcomm M (⨅ k, U (τ k)) (⨅ k, g ⁻¹ᵁ U (τ k))
      (le_of_eq (preimage_iInf_eq g fun k => U (τ k)).symm))
    (fun τ k => pullbackSectionsLinear_restrict g a a' φ hcomm M _ _ (cech_face_le U τ k)
      (cech_face_le (fun i => g ⁻¹ᵁ U i) τ k))

/-- The `ℤ`-graded termwise map: zero in negative degrees. -/
def cechPullbackTermZ (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules) :
    ∀ i : ℤ, (ModuleCat.restrictScalars a).obj (cechTermAltZ U M i) ⟶
      (ModuleCat.restrictScalars φ).obj ((ModuleCat.restrictScalars a').obj
        (cechTermAltZ (fun i => g ⁻¹ᵁ U i) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) i))
  | Int.ofNat p => cechPullbackTerm g a a' φ U hcomm M p
  | Int.negSucc _ => 0

theorem cechPullbackTermZ_comm (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    cechPullbackTermZ g a a' φ U hcomm M i ≫
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj
          (((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj
            (cechComplexAlt (fun i => g ⁻¹ᵁ U i)
              ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)))).d i j =
      (((ModuleCat.restrictScalars a).mapHomologicalComplex _).obj (cechComplexAlt U M)).d i j ≫
        cechPullbackTermZ g a a' φ U hcomm M j := by
  obtain rfl : i + 1 = j := hij
  cases i with
  | ofNat p =>
    have h1 := cechComplexAlt_d U M p
    have h2 := cechComplexAlt_d (fun i => g ⁻¹ᵁ U i)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) p
    show cechPullbackTerm g a a' φ U hcomm M p ≫
        (ModuleCat.restrictScalars φ).map ((ModuleCat.restrictScalars a').map
          ((cechComplexAlt (fun i => g ⁻¹ᵁ U i)
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).d (Int.ofNat p) (Int.ofNat p + 1))) =
      (ModuleCat.restrictScalars a).map ((cechComplexAlt U M).d (Int.ofNat p) (Int.ofNat p + 1)) ≫
        cechPullbackTerm g a a' φ U hcomm M (p + 1)
    rw [show (cechComplexAlt U M).d (Int.ofNat p) (Int.ofNat p + 1) = cechDiffAlt U M p from h1,
      show (cechComplexAlt (fun i => g ⁻¹ᵁ U i)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).d (Int.ofNat p) (Int.ofNat p + 1) =
        cechDiffAlt (fun i => g ⁻¹ᵁ U i) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) p from h2]
    exact cechPullbackTerm_comm g a a' φ U hcomm M p
  | negSucc k =>
    have hz : IsZero ((ModuleCat.restrictScalars a).obj (ModuleCat.of Γ(X, ⊤) PUnit)) :=
      Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton _)
    exact hz.eq_of_src _ _

/-- **The chain map** `Č(U, M)` (as a complex of `A`-modules) `→ Č(g⁻¹U, g^*M)` (as a complex of
`A'`-modules, restricted to `A` along `φ`). -/
def cechPullbackMap (hcomm : g.appTop.hom.comp a = a'.comp φ) (M : X.Modules) :
    ((ModuleCat.restrictScalars a).mapHomologicalComplex _).obj (cechComplexAlt U M) ⟶
      ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj
          (cechComplexAlt (fun i => g ⁻¹ᵁ U i)
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M))) where
  f := cechPullbackTermZ g a a' φ U hcomm M
  comm' := cechPullbackTermZ_comm g a a' φ U hcomm M

end Linear

end AlgebraicGeometry.Scheme.Modules

end
