import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SymGradedAlgebraLift

/-! # The universal property of the weighted symmetric algebra

Existence of the graded algebra morphism induced by generator maps.

`weightedSymAlgebra V = Sym(⊕_q V_q^∨)` with `V_q^∨` in weight `q+1`. A morphism of graded
QC algebras `weightedSymAlgebra V ⟶ T` is determined by where it sends the generators `V_q^∨ ⟶ T_{q+1}`, and every family
of such maps extends: this is the sheafified universal property of the symmetric algebra (Bourbaki, Algebra III §6 no. 1,
Prop. 2; Hartshorne II Ex. 5.16; Stacks 01CK–01CL for `Sym` of a sheaf of modules), applied factorwise to the recursive
definition `weightedSymTensor`. The **existence** statement `weightedSymAlgebra.exists_hom_of_gen` (a `Prop`) is what
`reesDeformation_restrictToLambda_zero_iso_weightedSym` needs to
build the comparison map `weightedSymAlgebra V ⟶ s₀^*R` from the generator maps
`V_q^∨ ≅ S_{q+1}/I^{(2)}_{q+1} ⟶ (s₀^*R)_{q+1}` (`reesDeformation.linearPieceToFiber`,
`DeformedJetAlgebraFiberAtZero_Generators`); the morphism itself is also available as `weightedSymAlgebra.liftHom`.

## Proof

Write `W_q := V_q^∨` (quasi-coherent because locally free: `isLocallyFree_dual'`, `isQuasicoherent_of_isLocallyFree`).
1. One factor (`…_WeightedSymLift_SymFactor`): `g_q : W_q ⟶ T_{q+1}` induces `symLift : Sym^d W_q ⟶ T_{(q+1) d}`
   (descent of the `d`-fold product along `symPowπ`), a graded monoid homomorphism `Sym(W_q) → T` along `d ↦ (q+1) d`,
   with `symGen ≫ symLift 1 = g_q`.
2. All factors (this file): by recursion on `r` along `weightedSymTensor`, `weightedSymTensorLift : ⊗_q Sym^{d_q} W_q ⟶
   T_{wsum wt d}` is `(symLift ⊗ recursive) ≫ T.mul`, where `wsum wt d = Σ_q wt_q d_q` (recursively defined so that the
   indices match by definition). It is a graded monoid homomorphism (`IsGradedMonoidHom.consTensor`, using the middle-four
   interchange in the commutative `T`, `…_WeightedSymLift_GradedMonoidHom`), and it sends the generator
   `weightedSymTensorGen` to `g_j` (`weightedSymTensorGen_comp_weightedSymTensorLift`, by the same recursion, using
   `one_mul`/`mul_one` of `T`).
3. The morphism: `app m := biproduct.desc (fun d => weightedSymTensorLift (dv d) ≫ eqToHom (d.2))` on
   `part V m = ⊕_{d ∈ D_m} term V d`; `map_mul` by `ext₂` and `ι_tensor_ι_comp_mulHom`, `map_one` from `oneHom`, and the
   generator identity from `genIncl = weightedSymTensorGen ≫ ι_{single j}` and `biproduct.ι_desc`.
Edge cases: `r = 0` (no generators; `app 0 = T.one` on the single summand); `X = ∅` (nothing special).

Source: Bourbaki, Algebra III §6 no. 1, Prop. 2 (universal property of `Sym`); Lemma 2.3 of the paper
(the weighted symmetric algebra and its appearance as the fiber at `λ = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} (T : X.GradedQCAlgebra)

/-! ## The weight `wsum wt d = Σ_q wt_q d_q`, defined recursively along `Fin r` -/

/-- `wsum r wt d = Σ_{q < r} wt q * d q`, recursively (so that the recursion of `weightedSymTensorLift` typechecks by
definition). -/
def wsum : (r : ℕ) → (Fin r → ℕ) → (Fin r → ℕ) → ℕ
  | 0, _, _ => 0
  | r + 1, wt, d => wt 0 * d 0 + wsum r (Fin.tail wt) (Fin.tail d)

theorem wsum_add : ∀ (r : ℕ) (wt d d' : Fin r → ℕ), wsum r wt (d + d') = wsum r wt d + wsum r wt d'
  | 0, _, _, _ => rfl
  | r + 1, wt, d, d' => by
    show wt 0 * (d 0 + d' 0) + wsum r (Fin.tail wt) (Fin.tail d + Fin.tail d') = _
    rw [wsum_add r, Nat.mul_add]
    show _ = wt 0 * d 0 + wsum r (Fin.tail wt) (Fin.tail d) + (wt 0 * d' 0 + wsum r (Fin.tail wt) (Fin.tail d'))
    omega

theorem wsum_zero : ∀ (r : ℕ) (wt : Fin r → ℕ), wsum r wt 0 = 0
  | 0, _ => rfl
  | r + 1, wt => by
    show wt 0 * 0 + wsum r (Fin.tail wt) 0 = 0
    rw [wsum_zero r, Nat.mul_zero]

theorem wsum_eq_sum : ∀ (r : ℕ) (wt d : Fin r → ℕ), wsum r wt d = ∑ q, wt q * d q
  | 0, _, _ => by simp [wsum]
  | r + 1, wt, d => by
    rw [Fin.sum_univ_succ, ← wsum_eq_sum r]
    rfl

/-- The weight of the multi-degree `δ_j` is `wt j`. -/
theorem wsum_single (r : ℕ) (wt : Fin r → ℕ) (j : Fin r) (e : Fin r → ℕ)
    (he : ∀ q, e q = if q = j then 1 else 0) : wt j = wsum r wt e := by
  rw [wsum_eq_sum, Finset.sum_eq_single j]
  · simp [he]
  · intro b _ hb; simp [he, hb]
  · simp

/-! ## The lift on the recursive tensor `⊗_q Sym^{d_q} W_q` -/

/-- `⊗_q Sym^{d_q}(W_q) ⟶ T_{wsum wt d}`: `(symLift ⊗ recursive) ≫ T.mul`, `T.one` for `r = 0`. -/
def weightedSymTensorLift : (r : ℕ) → (W : Fin r → X.Modules) → (∀ q, (W q).IsQuasicoherent) →
    (wt : Fin r → ℕ) → (∀ q, W q ⟶ T.part (wt q)) → (d : Fin r → ℕ) →
    (AlgebraicGeometry.Scheme.weightedSymTensor r W d ⟶ T.part (wsum r wt d))
  | 0, _, _, _, _, _ => T.one
  | r + 1, W, hW, wt, g, d =>
    (Modules.symLift T (hW 0) (g 0) (d 0) ⊗ₘ
        weightedSymTensorLift r (Fin.tail W) (fun q => hW q.succ) (Fin.tail wt) (fun q => g q.succ) (Fin.tail d)) ≫
      T.mul _ _

/-- The lift is a graded monoid homomorphism along `wsum wt`. -/
theorem weightedSymTensorLift_isGradedMonoidHom : ∀ (r : ℕ) (W : Fin r → X.Modules)
    (hW : ∀ q, (W q).IsQuasicoherent) (wt : Fin r → ℕ) (g : ∀ q, W q ⟶ T.part (wt q)),
    MiyaokaMori.IsGradedMonoidHom (AlgebraicGeometry.Scheme.weightedSymTensor r W)
      (AlgebraicGeometry.Scheme.weightedSymTensorMul r W) (AlgebraicGeometry.Scheme.weightedSymTensorOne r W)
      T.part T.mul T.one (wsum r wt) (wsum_add r wt) (wsum_zero r wt) (weightedSymTensorLift T r W hW wt g)
  | 0, _, _, _, _ => MiyaokaMori.IsGradedMonoidHom.unit T.isGradedMonoid
  | r + 1, W, hW, wt, g =>
    MiyaokaMori.IsGradedMonoidHom.consTensor T.isGradedMonoid
      (Modules.symLift_isGradedMonoidHom T (hW 0) (g 0))
      (weightedSymTensorLift_isGradedMonoidHom r (Fin.tail W) (fun q => hW q.succ) (Fin.tail wt)
        (fun q => g q.succ))
      (wsum_add (r + 1) wt) (wsum_zero (r + 1) wt)

/-- `eqToHom` on the index commutes with a family of morphisms. -/
theorem eqToHom_comp_family {ι : Type*} {P Q' : ι → X.Modules} (Ψ : ∀ a, P a ⟶ Q' a) {a b : ι} (h : a = b) :
    eqToHom (congrArg P h) ≫ Ψ b = Ψ a ≫ eqToHom (congrArg Q' h) := by
  subst h; simp

/-- The lift sends the generator `weightedSymTensorGen` (the `j`-th factor `symGen`, the others `one`) to `g j`. -/
theorem weightedSymTensorGen_comp_weightedSymTensorLift : ∀ (r : ℕ) (W : Fin r → X.Modules)
    (hW : ∀ q, (W q).IsQuasicoherent) (wt : Fin r → ℕ) (g : ∀ q, W q ⟶ T.part (wt q)) (j : Fin r)
    (e : Fin r → ℕ) (he : ∀ q, e q = if q = j then 1 else 0),
    AlgebraicGeometry.Scheme.weightedSymTensorGen r W j e he ≫ weightedSymTensorLift T r W hW wt g e =
      g j ≫ eqToHom (congrArg T.part (wsum_single r wt j e he))
  | 0, _, _, _, _, j, _, _ => j.elim0
  | r + 1, W, hW, wt, g, ⟨0, h0⟩, e, he => by
    have h1 : (1 : ℕ) = e 0 := by rw [he 0]; simp
    have h2 : (0 : Fin r → ℕ) = Fin.tail e := funext fun q => by
      rw [Fin.tail, he q.succ]; simp [Fin.ext_iff]
    have hj : (⟨0, h0⟩ : Fin (r + 1)) = 0 := Fin.ext rfl
    show eqToHom (congrArg W hj) ≫ (ρ_ (W 0)).inv ≫
        ((Modules.symGen (W 0) ≫ eqToHom (congrArg (Modules.symGradedAlgebra (W 0)).part h1)) ⊗ₘ
          (AlgebraicGeometry.Scheme.weightedSymTensorOne r (Fin.tail W) ≫
            eqToHom (congrArg (AlgebraicGeometry.Scheme.weightedSymTensor r (Fin.tail W)) h2))) ≫
        ((Modules.symLift T (hW 0) (g 0) (e 0) ⊗ₘ
          weightedSymTensorLift T r (Fin.tail W) (fun q => hW q.succ) (Fin.tail wt) (fun q => g q.succ)
            (Fin.tail e)) ≫ T.mul _ _) =
      g ⟨0, h0⟩ ≫ eqToHom (congrArg T.part (wsum_single (r + 1) wt ⟨0, h0⟩ e he))
    rw [← Category.assoc (_ ⊗ₘ _), tensorHom_comp_tensorHom, Category.assoc, Category.assoc,
      eqToHom_comp_family (Modules.symLift T (hW 0) (g 0)) h1,
      eqToHom_comp_family
        (weightedSymTensorLift T r (Fin.tail W) (fun q => hW q.succ) (Fin.tail wt) (fun q => g q.succ)) h2,
      ← Category.assoc (Modules.symGen (W 0)), Modules.symGen_comp_symLift,
      ← Category.assoc (AlgebraicGeometry.Scheme.weightedSymTensorOne r (Fin.tail W)),
      (weightedSymTensorLift_isGradedMonoidHom T r (Fin.tail W) (fun q => hW q.succ) (Fin.tail wt)
        (fun q => g q.succ)).map_one]
    simp only [Category.assoc, eqToHom_trans]
    have ha : wt 0 = wt 0 * e 0 := by rw [← h1, Nat.mul_one]
    have hb : (0 : ℕ) = wsum r (Fin.tail wt) (Fin.tail e) := by rw [← h2, wsum_zero]
    rw [← tensorHom_comp_tensorHom, Category.assoc, ← MiyaokaMori.gmul_rfl T.part T.mul,
      MiyaokaMori.eqToHom_tensorHom_comp_gmul T.part T.mul ha hb rfl, tensorHom_def, Category.assoc,
      T.isGradedMonoid.gmul_mul_one _ (by exact wsum_single (r + 1) wt ⟨0, h0⟩ e he),
      ← Category.assoc (g 0 ▷ _), rightUnitor_naturality, Category.assoc, Iso.inv_hom_id_assoc,
      ← Category.assoc, eqToHom_comp_family g hj, Category.assoc, eqToHom_trans]
    try rfl
  | r + 1, W, hW, wt, g, ⟨j + 1, hj⟩, e, he => by
    have h1 : (0 : ℕ) = e 0 := by rw [he 0]; simp [Fin.ext_iff]
    have hj' : j < r := by omega
    have he' : ∀ q : Fin r, e q.succ = if q = ⟨j, hj'⟩ then 1 else 0 := fun q => by
      rw [he q.succ]; simp [Fin.ext_iff]
    have hrec := weightedSymTensorGen_comp_weightedSymTensorLift r (fun i => W i.succ) (fun q => hW q.succ)
      (fun i => wt i.succ) (fun q => g q.succ) ⟨j, hj'⟩ (fun i => e i.succ) he'
    have ha : (0 : ℕ) = wt 0 * e 0 := by rw [← h1, Nat.mul_zero]
    have hb : wt (Fin.succ ⟨j, hj'⟩) = wsum r (fun i => wt i.succ) (fun i => e i.succ) :=
      wsum_single r (fun i => wt i.succ) ⟨j, hj'⟩ (fun i => e i.succ) he'
    show (λ_ (W (Fin.succ ⟨j, hj'⟩))).inv ≫
        (((Modules.symGradedAlgebra (W 0)).one ≫ eqToHom (congrArg (Modules.symGradedAlgebra (W 0)).part h1)) ⊗ₘ
          AlgebraicGeometry.Scheme.weightedSymTensorGen r (fun i => W i.succ) ⟨j, hj'⟩ (fun i => e i.succ) he') ≫
        ((Modules.symLift T (hW 0) (g 0) (e 0) ⊗ₘ
          weightedSymTensorLift T r (fun i => W i.succ) (fun q => hW q.succ) (fun i => wt i.succ)
            (fun q => g q.succ) (fun i => e i.succ)) ≫ T.mul _ _) =
      g ⟨j + 1, hj⟩ ≫ eqToHom (congrArg T.part (wsum_single (r + 1) wt ⟨j + 1, hj⟩ e he))
    rw [← Category.assoc (_ ⊗ₘ _), tensorHom_comp_tensorHom, Category.assoc,
      eqToHom_comp_family (Modules.symLift T (hW 0) (g 0)) h1,
      ← Category.assoc (Modules.symGradedAlgebra (W 0)).one,
      (Modules.symLift_isGradedMonoidHom T (hW 0) (g 0)).map_one, hrec]
    simp only [Category.assoc, eqToHom_trans]
    rw [← tensorHom_comp_tensorHom, Category.assoc, ← MiyaokaMori.gmul_rfl T.part T.mul,
      MiyaokaMori.eqToHom_tensorHom_comp_gmul T.part T.mul ha hb rfl, tensorHom_def', Category.assoc,
      T.isGradedMonoid.gmul_one_mul _ (by exact wsum_single (r + 1) wt ⟨j + 1, hj⟩ e he),
      ← Category.assoc (_ ◁ _), leftUnitor_naturality, Category.assoc, Iso.inv_hom_id_assoc]
    try rfl

/-! ## Assembly on `weightedSymAlgebra V` -/

namespace weightedSymAlgebra

variable {r : ℕ} (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType]

/-- The generator sheaves `V_q^∨` are quasi-coherent (locally free of finite type ⇒ dual locally free). -/
theorem gen_isQuasicoherent (q : Fin r) : (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V q).IsQuasicoherent :=
  haveI := Modules.isLocallyFree_dual' (V q)
  Modules.isQuasicoherent_of_isLocallyFree (Modules.dual (V q))

variable (g : ∀ q : Fin r, Modules.dual (V q) ⟶ T.part (q.1 + 1))

/-- The recursive lift, specialized to the generators `V_q^∨` in weights `q + 1`. -/
abbrev liftTensor (d : Fin r → ℕ) :
    AlgebraicGeometry.Scheme.weightedSymTensor r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) d ⟶
      T.part (wsum r (fun q => q.1 + 1) d) :=
  weightedSymTensorLift T r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) (gen_isQuasicoherent V)
    (fun q => q.1 + 1) g d

theorem wsum_dv {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) :
    wsum r (fun q => q.1 + 1) (dv d) = m := by
  rw [wsum_eq_sum]; exact d.2

/-- The lift on the summand `term V d` of `part V m`. -/
def liftTerm {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d ⟶ T.part m :=
  liftTensor T V g (dv d) ≫ eqToHom (congrArg T.part (wsum_dv d))

/-- The graded pieces of the induced morphism. -/
def liftApp (m : ℕ) : AlgebraicGeometry.Scheme.weightedSymAlgebra.part V m ⟶ T.part m :=
  biproduct.desc fun d => liftTerm T V g d

theorem ι_comp_liftApp {m : ℕ} (d : AlgebraicGeometry.Scheme.weightedSymIndex r m) :
    biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d) d ≫ liftApp T V g m =
      liftTerm T V g d :=
  biproduct.ι_desc _ _

theorem liftApp_map_mul (m n : ℕ) :
    mulHom V m n ≫ liftApp T V g (m + n) = (liftApp T V g m ⊗ₘ liftApp T V g n) ≫ T.mul m n := by
  apply ext₂
  intro a b
  have hΨ := weightedSymTensorLift_isGradedMonoidHom T r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V)
    (gen_isQuasicoherent V) (fun q => q.1 + 1) g
  have hidx : wsum r (fun q => q.1 + 1) (dv a) + wsum r (fun q => q.1 + 1) (dv b) =
      wsum r (fun q => q.1 + 1) (dv (a.add b)) :=
    (wsum_add r (fun q => q.1 + 1) (dv a) (dv b)).symm
  have h : mulTerm V a b ≫ liftTensor T V g (dv (a.add b)) =
      (liftTensor T V g (dv a) ⊗ₘ liftTensor T V g (dv b)) ≫ MiyaokaMori.gmul T.part T.mul hidx :=
    hΨ.map_mul (dv a) (dv b)
  rw [← Category.assoc, ι_tensor_ι_comp_mulHom, Category.assoc, ι_comp_liftApp, ← Category.assoc,
    tensorHom_comp_tensorHom, ι_comp_liftApp, ι_comp_liftApp, liftTerm, ← Category.assoc, h, liftTerm, liftTerm,
    ← tensorHom_comp_tensorHom, Category.assoc, Category.assoc, ← MiyaokaMori.gmul_rfl T.part T.mul m n,
    MiyaokaMori.eqToHom_tensorHom_comp_gmul T.part T.mul (wsum_dv a) (wsum_dv b) rfl,
    MiyaokaMori.gmul_comp_eqToHom T.part T.mul hidx (wsum_dv (a.add b))]

theorem liftApp_map_one : oneHom V ≫ liftApp T V g 0 = T.one := by
  have hΨ := weightedSymTensorLift_isGradedMonoidHom T r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V)
    (gen_isQuasicoherent V) (fun q => q.1 + 1) g
  have h : AlgebraicGeometry.Scheme.weightedSymTensorOne r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) ≫
      liftTensor T V g (dv (⟨0, by simp⟩ : AlgebraicGeometry.Scheme.weightedSymIndex r 0)) =
        T.one ≫ eqToHom (congrArg T.part (wsum_zero r (fun q => q.1 + 1)).symm) :=
    hΨ.map_one
  rw [oneHom, Category.assoc, ι_comp_liftApp, liftTerm, ← Category.assoc, h, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- **The morphism `weightedSymAlgebra V ⟶ T` induced by generator maps `g_q : V_q^∨ ⟶ T_{q+1}`.** -/
def liftHom : AlgebraicGeometry.Scheme.weightedSymAlgebra V ⟶ T where
  app := liftApp T V g
  map_mul := liftApp_map_mul T V g
  map_one := liftApp_map_one T V g

/-- The induced morphism sends the generator `genIncl V q : V_q^∨ ⟶ (weightedSymAlgebra V)_{q+1}` to `g q`. -/
theorem genIncl_comp_liftHom (q : Fin r) :
    AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V q ≫ (liftHom T V g).app (q.1 + 1) = g q := by
  show (AlgebraicGeometry.Scheme.weightedSymTensorGen r (AlgebraicGeometry.Scheme.weightedSymAlgebra.gen V) q
      (dv (AlgebraicGeometry.Scheme.weightedSymIndex.single q)) _ ≫
      biproduct.ι (fun d => AlgebraicGeometry.Scheme.weightedSymAlgebra.term V d)
        (AlgebraicGeometry.Scheme.weightedSymIndex.single q)) ≫ liftApp T V g (q.1 + 1) = g q
  rw [Category.assoc, ι_comp_liftApp, liftTerm, ← Category.assoc,
    weightedSymTensorGen_comp_weightedSymTensorLift, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

end weightedSymAlgebra

end AlgebraicGeometry.Scheme

/-- **Universal property of `weightedSymAlgebra` (existence).** Given a graded QC algebra `T` and maps
`g_q : V_q^∨ ⟶ T_{q+1}`, there is a morphism of graded QC algebras `φ : weightedSymAlgebra V ⟶ T` with
`genIncl V q ≫ φ.app (q+1) = g_q` for all `q`.

Proof: `φ := weightedSymAlgebra.liftHom T V g` and `weightedSymAlgebra.genIncl_comp_liftHom` (see the module docstring
for the route). -/
theorem AlgebraicGeometry.Scheme.weightedSymAlgebra.exists_hom_of_gen {X : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : Fin r → X.Modules) [∀ q, (V q).IsLocallyFree] [∀ q, (V q).IsFiniteType] (T : X.GradedQCAlgebra)
    (g : ∀ q : Fin r, AlgebraicGeometry.Scheme.Modules.dual (V q) ⟶ T.part (q.1 + 1)) :
    ∃ φ : AlgebraicGeometry.Scheme.weightedSymAlgebra V ⟶ T,
      ∀ q : Fin r, AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl V q ≫ φ.app (q.1 + 1) = g q :=
  ⟨AlgebraicGeometry.Scheme.weightedSymAlgebra.liftHom T V g,
    AlgebraicGeometry.Scheme.weightedSymAlgebra.genIncl_comp_liftHom T V g⟩

end
