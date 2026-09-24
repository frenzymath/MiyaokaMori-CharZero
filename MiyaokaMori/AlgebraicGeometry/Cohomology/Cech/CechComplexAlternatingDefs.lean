import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingLocalizationAcyclic

/-! # Terms and differential of the alternating Čech complex

The alternating Čech cochains and differential of a module on a family of opens (the `p`-th term is
`∏_{i_0<⋯<i_p} Γ(M, U_{i_0} ∩ ⋯ ∩ U_{i_p})`, the differential the alternating sum of restriction
maps), together with `d ∘ d = 0` at the categorical level:
`cechDiffAlt U M q ≫ cechDiffAlt U M (q+1) = 0`.

Proof sketch:
1. Elements of the categorical product `∏ᶜ` are exchanged with families of sections
   (`ModuleCat.piIsoPi`, `cechToFamily_bijective`); compatibility of `Pi.lift`/`Pi.π` gives
   `(d x)_τ = Σ_k (-1)^k res(x_{τ minus k})` (`cechToFamily_diff`).
2. The alternating differential on families equals the abstract differential `CechAltAlg.d` of
   `CechAlternatingLocalizationAcyclic.lean` (with `A = ℤ`, `famD_eq`), so the abstract
   `CechAltAlg.d_comp_d` gives `cechFamilyD_comp`.
3. `cechDiffAlt_comp` follows from 1, 2 and the bijectivity of `cechToFamily`; it is the nonnegative
   part of `cechDiffAltZ_comp`.

Source: Stacks 01FG (the alternating Čech complex).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The sections `Γ(M, V)` as a `Γ(X, ⊤)`-module: restriction of scalars along the restriction
ring homomorphism `Γ(X, ⊤) → Γ(X, V)`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.sectionsOverTop {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (V : X.Opens) : ModuleCat.{u} Γ(X, ⊤) :=
  (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom).obj
    (M.val.obj (Opposite.op V))

/-- Functoriality of the restriction ring homomorphisms: `Γ(X,⊤) → Γ(X,W)` equals
`Γ(X,⊤) → Γ(X,V) → Γ(X,W)`. -/

theorem AlgebraicGeometry.Scheme.Modules.sectionsOverTop_ringHom_comp {X : AlgebraicGeometry.Scheme.{u}}
    {V W : X.Opens} (h : W ≤ V) :
    (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE (le_top : W ≤ ⊤)).op).hom =
      (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE h).op).hom.comp
        (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom := by
  rw [← RingCat.hom_comp, ← CategoryTheory.Functor.map_comp]; rfl

/-- The restriction map `Γ(M, V) → Γ(M, W)` for `W ≤ V`, as a `Γ(X, ⊤)`-linear map (the restriction
map of `M` followed by the composition isomorphism of restriction of scalars). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.sectionsOverTopRestrict {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) {V W : X.Opens} (h : W ≤ V) :
    M.sectionsOverTop V ⟶ M.sectionsOverTop W :=
  (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom).map
      (M.val.map (CategoryTheory.homOfLE h).op) ≫
    (ModuleCat.restrictScalarsComp'App _ _ _
      (AlgebraicGeometry.Scheme.Modules.sectionsOverTop_ringHom_comp h) (M.val.obj (Opposite.op W))).inv

/-- The `p`-th term (`p ≥ 0`): `∏_{σ : Fin (p+1) ↪o Fin n} Γ(M, ⨅ j, U (σ j))`; for `p + 1 > n` the
index set is empty and the product is `0`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.cechTermAlt {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) (p : ℕ) : ModuleCat.{u} Γ(X, ⊤) :=
  ∏ᶜ fun σ : Fin (p + 1) ↪o Fin n => M.sectionsOverTop (⨅ j, U (σ j))

/-- Removing the `j`-th index: `U_{τ_0} ∩ ⋯ ∩ U_{τ_{p+1}} ⊆ U_{τ ∘ δ_j}`. -/

theorem AlgebraicGeometry.Scheme.Modules.cech_face_le {X : AlgebraicGeometry.Scheme.{u}} {n p : ℕ}
    (U : Fin n → X.Opens) (τ : Fin (p + 2) ↪o Fin n) (j : Fin (p + 2)) :
    (⨅ k, U (τ k)) ≤ ⨅ k, U (((Fin.succAboveOrderEmb j).trans τ) k) :=
  le_iInf fun k => iInf_le (fun i => U (τ i)) (j.succAbove k)

/-- The differential `d(s)_τ = Σ_j (-1)^j · res(s_{τ ∘ δ_j})`, `δ_j = Fin.succAboveOrderEmb j`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.cechDiffAlt {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) (p : ℕ) :
    AlgebraicGeometry.Scheme.Modules.cechTermAlt U M p ⟶ AlgebraicGeometry.Scheme.Modules.cechTermAlt U M (p + 1) :=
  CategoryTheory.Limits.Pi.lift fun τ : Fin (p + 2) ↪o Fin n =>
    ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (CategoryTheory.Limits.Pi.π (fun σ : Fin (p + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k)))
          ((Fin.succAboveOrderEmb j).trans τ) ≫
        M.sectionsOverTopRestrict (AlgebraicGeometry.Scheme.Modules.cech_face_le U τ j))

/-- The `ℤ`-graded terms: `cechTermAlt` in nonnegative degrees, `0` in negative degrees. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.cechTermAltZ {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) : ℤ → ModuleCat.{u} Γ(X, ⊤)
  | Int.ofNat p => AlgebraicGeometry.Scheme.Modules.cechTermAlt U M p
  | Int.negSucc _ => ModuleCat.of Γ(X, ⊤) PUnit

noncomputable def AlgebraicGeometry.Scheme.Modules.cechDiffAltZ {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ}
    (U : Fin n → X.Opens) (M : X.Modules) :
    ∀ i : ℤ, AlgebraicGeometry.Scheme.Modules.cechTermAltZ U M i ⟶
      AlgebraicGeometry.Scheme.Modules.cechTermAltZ U M (i + 1)
  | Int.ofNat p => AlgebraicGeometry.Scheme.Modules.cechDiffAlt U M p
  | Int.negSucc _ => 0

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens) (M : X.Modules)

/-- Alternating cochains as families of sections. -/
abbrev CechFamily (q : ℕ) : Type u := ∀ σ : Fin (q + 1) ↪o Fin n, Γ(M, ⨅ j, U (σ j))

/-- The alternating differential on families of sections. -/
def cechFamilyD (q : ℕ) (t : CechFamily U M q) : CechFamily U M (q + 1) := fun τ =>
  ∑ k : Fin (q + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    M.presheaf.map (homOfLE (cech_face_le U τ k)).op (t ((Fin.succAboveOrderEmb k).trans τ))

/-- From an element of the categorical product to a family of sections. -/
def cechToFamily (q : ℕ) (x : cechTermAlt U M q) : CechFamily U M q := fun σ =>
  (Pi.π (fun σ : Fin (q + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k))) σ).hom x

theorem pi_lift_sum_apply {R : Type u} [Ring R] {ι κ : Type} {Z : ι → ModuleCat.{u} R}
    {W : κ → ModuleCat.{u} R} {m : ℕ} (a : κ → Fin m → ι) (ε : Fin m → ℤ)
    (r : ∀ (τ : κ) (k : Fin m), Z (a τ k) ⟶ W τ) (x : ↑(∏ᶜ Z)) (τ : κ) :
    (Pi.π W τ).hom ((Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z (a τ k) ≫ r τ k)).hom x) =
      ∑ k : Fin m, ε k • (r τ k).hom ((Pi.π Z (a τ k)).hom x) := by
  have h : (Pi.lift fun τ : κ => ∑ k : Fin m, ε k • (Pi.π Z (a τ k) ≫ r τ k)) ≫ Pi.π W τ = _ :=
    Pi.lift_π _ τ
  have h2 := congrArg (fun φ => φ.hom x) h
  refine Eq.trans h2 ?_
  simp [ModuleCat.hom_sum, LinearMap.sum_apply]

theorem cechToFamily_diff (q : ℕ) (x : cechTermAlt U M q) :
    cechToFamily U M (q + 1) ((cechDiffAlt U M q).hom x) = cechFamilyD U M q (cechToFamily U M q x) := by
  funext τ
  exact pi_lift_sum_apply (Z := fun σ : Fin (q + 1) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k)))
    (W := fun σ : Fin (q + 2) ↪o Fin n => M.sectionsOverTop (⨅ k, U (σ k)))
    (fun τ k => (Fin.succAboveOrderEmb k).trans τ) (fun k => (-1 : ℤ) ^ (k : ℕ))
    (fun τ k => M.sectionsOverTopRestrict (cech_face_le U τ k)) x τ

theorem pi_family_bijective {R : Type u} [Ring R] {ι : Type} (Z : ι → ModuleCat.{u} R) :
    Function.Bijective (fun (x : ↑(∏ᶜ Z)) (i : ι) => (Pi.π Z i).hom x) := by
  have h : (fun (x : ↑(∏ᶜ Z)) (i : ι) => (Pi.π Z i).hom x) = ⇑(ModuleCat.piIsoPi Z).hom.hom := by
    funext x i
    exact (ModuleCat.piIsoPi_hom_ker_subtype_apply Z i x).symm
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi Z).hom

theorem cechToFamily_bijective (q : ℕ) : Function.Bijective (cechToFamily U M q) :=
  pi_family_bijective _

/-- The restriction map (`ℤ`-linear). -/
def famRes {v w : X.Opens} (h : w ≤ v) : Γ(M, v) →ₗ[ℤ] Γ(M, w) :=
  (M.presheaf.map (homOfLE h).op).hom.toIntLinearMap

theorem famRes_comp {u v w : X.Opens} (h : v ≤ u) (h' : w ≤ v) (x : Γ(M, u)) :
    famRes M h' (famRes M h x) = famRes M (h'.trans h) x := by
  show M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op x) =
    M.presheaf.map (homOfLE (h'.trans h)).op x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The differential on families equals the abstract alternating differential (`A = ℤ`). -/
theorem famD_eq (q : ℕ) (t : CechFamily U M q) :
    CechAltAlg.d (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
      (fun W : X.Opens => Γ(M, W)) (fun h => famRes M h) (fun _ τ k => cech_face_le U τ k) q t =
      cechFamilyD U M q t := by
  funext σ
  exact CechAltAlg.d_apply (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
      (fun W : X.Opens => Γ(M, W)) (fun h => famRes M h) (fun q τ k => cech_face_le U τ k) q t σ

/-- `d ∘ d = 0` on families of sections (from the abstract lemma `CechAltAlg.d_comp_d`). -/
theorem cechFamilyD_comp (q : ℕ) (t : CechFamily U M q) :
    cechFamilyD U M (q + 1) (cechFamilyD U M q t) = 0 := by
  have key := CechAltAlg.d_comp_d (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
      (fun W : X.Opens => Γ(M, W)) (fun h => famRes M h) (fun q τ k => cech_face_le U τ k)
      (fun h h' x => famRes_comp M h h' x) q t
  rw [famD_eq U M q t, famD_eq U M (q + 1)] at key
  exact key

/-- The differential on families preserves subtraction. -/
theorem cechFamilyD_sub (q : ℕ) (t t' : CechFamily U M q) :
    cechFamilyD U M q (t - t') = cechFamilyD U M q t - cechFamilyD U M q t' := by
  have key := map_sub (CechAltAlg.d (A := ℤ) (fun q (σ : Fin (q + 1) ↪o Fin n) => ⨅ k, U (σ k))
      (fun W : X.Opens => Γ(M, W)) (fun h => famRes M h) (fun _ τ k => cech_face_le U τ k) q) t t'
  rw [famD_eq U M q t, famD_eq U M q t', famD_eq U M q (t - t')] at key
  exact key

/-- `d ∘ d = 0` at the categorical level, without going through `cechComplexAlt` (whose definition
needs this fact). -/
theorem cechDiffAlt_comp (q : ℕ) : cechDiffAlt U M q ≫ cechDiffAlt U M (q + 1) = 0 := by
  ext x
  apply (cechToFamily_bijective U M (q + 2)).1
  show cechToFamily U M (q + 2) ((cechDiffAlt U M (q + 1)).hom ((cechDiffAlt U M q).hom x)) =
    cechToFamily U M (q + 2) 0
  rw [cechToFamily_diff, cechToFamily_diff, cechFamilyD_comp]
  funext τ
  exact (map_zero _).symm

end AlgebraicGeometry.Scheme.Modules

end
