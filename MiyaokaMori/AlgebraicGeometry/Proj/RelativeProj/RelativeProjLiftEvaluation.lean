import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLift
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesEpiOfOpenCover
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_EpiTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamily
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback

/-! # Evaluation of the lift into a relative Proj

Statement: let `S` be a graded quasi-coherent algebra on a scheme `X`, `g : T → X`, `M` a line bundle on `T`,
`D = (Ψ_m : g^*S_m → M^{⊗m})_m` the input data of `relativeProj.lift` (preserving unit and multiplication,
locally surjective in some positive degree), and `τ = relativeProj.lift S g M D : T → Proj_X S`. Then
(a) for every `m`, `Ψ_m` (transported along `(τ≫π)^* ≅ g^*`) is induced by `τ` (`relativeProj.InducedBy`): there is
`ψ_m : τ^*O(m) → M^{⊗m}` with `Ψ_m = (τ^*π^*S_m ≅ (τ≫π)^*S_m)⁻¹ ≫ τ^*(evaluation π^*S_m → O(m)) ≫ ψ_m`;
(b) if `m` is sufficiently divisible (`m > 0` and the Veronese subalgebra `S^{(m)}` is generated in degree one),
then `Ψ_m` is an epimorphism.

Proof sketch:
1. (a) Local construction of `ψ_m`. Take a piece of the definition of `lift`: an affine open `V' ⊆ U ⊓ g⁻¹W`
   (`W ⊆ X` affine open, `e : M|_U ≅ O_U`), with `τ|_{V'} = Proj.fromOfGlobalSections(liftLocalRingHom)` followed
   by `π⁻¹W ≅ Proj A(W)` (`A(W) = ⊕_m Γ(W, S_m)`, the `affineIso` of Stacks 01NQ). `O(m)|_{π⁻¹W}` is the pullback
   of `Proj.twist A(W) m` (the `twistAffineIso` of Stacks 01NR), whose sections on `D₊(r)` (`r ∈ A(W)_d`, `d > 0`)
   are `A(W)(m)_{(r)} = { a / r^k : a ∈ A(W)_{m+kd} }` (Stacks 01MN). On `V'_r := τ⁻¹D₊(r) = { liftLocalRingHom(r)
   invertible }` set `ψ_m(a / r^k) := Φ(a) · Φ(r)^{-k} · e^{-⊗m}(1) ∈ Γ(V'_r, M^{⊗m})`, with `Φ` the corresponding
   component of `liftLocalRingHom`; `Φ` is a ring homomorphism (by `D.map_one`, `D.map_mul`), hence compatible
   with the equivalence relation of fractions, and `Γ(V'_r, O)`-linear.
2. (a) Gluing. Change of `r`: on `D₊(r) ⊓ D₊(r') = D₊(rr')` the two formulas agree (common denominators).
   Change of trivialization `e ↝ u·e` (`u` a unit): the degree-`n` component of `Φ` is multiplied by `u^n`,
   `Φ(a)Φ(r)^{-k}` by `u^{m+kd}·u^{-kd} = u^m`, and `e^{-⊗m}(1)` by `u^{-m}`; they cancel. Change `W ⊇ W₃`:
   `liftLocalRingHom` is compatible with the restriction `A(W) → A(W₃)`, and `twistAffineIso` with restriction
   (Stacks 01NP/01NR). The same verifications as for the gluing of `lift` (`liftLocal_compat`), so the local `ψ_m`
   glue to `ψ_m : τ^*O(m) → M^{⊗m}`.
3. (a) The factorization. The evaluation map `relativeProj.evaluation S m` sends `x ∈ Γ(W, S_m)` over affine `W` to
   the section `x/1` (Stacks 01MN, `Proj.twistSection`), and `ψ_m(x/1) = Φ(x)·e^{-⊗m}(1)`, which by definition of
   `liftLocalRingHom` is the value of `Ψ_m` on the pullback of `x`, read through `e^{⊗m}`. `W` is affine and
   `S_m` quasi-coherent, so the pullbacks of `Γ(W, S_m)` generate `g^*S_m|_{V'}`, and two `O_T`-linear maps
   agreeing on generators agree; the transport between `(τ≫π)^*` and `g^*` is `lift_hom` (`pullbackCongr`).
4. (b) Epimorphisms in `Modules` can be checked locally on an open cover (`Modules.epi_of_openCover`). On the
   neighbourhood `U_t` given by `D.generates`, `map_mul` (tensoring preserves epimorphisms, `Modules.epi_tensorHom`;
   the pullback functor is strong monoidal and preserves epimorphisms) gives that `Ψ_{kn}` is epi. Using the
   Veronese `mulPowOne`, `Θ_ℓ := f^*(mulPowOne ℓ) ≫ Ψ_{ℓm}` unfolds to `… ≫ (Θ_{ℓ-1} ▷ _) ≫ (M^{⊗(ℓ-1)m} ◁ Ψ_m) ≫ iso`,
   so `M^{⊗(ℓ-1)m} ◁ Ψ_m` is epi, and whiskering with a line bundle reflects epimorphisms
   (`Modules.epi_of_epi_whiskerLeft`, using `L ⊗ L^∨ ≅ 𝟙`).

Part (a), `lift_inducedBy`, is assembled from `LiftData.exists_twistFamily_of_piece` (E) and
`LiftData.twistFamily_sectionMap_unique` (U) of `RelativeProjLiftEvaluationTwistFamily.lean` (a "twist family" in
all degrees with multiplicativity is unique, so no chart is ever changed).

Source: Stacks 01O4, 01N8 (morphisms to a relative Proj and the pullback of `O(n)`: `r^*O_{U_d}(nd) ≅ L^{⊗n}`),
01MN, 01NR. Used for the pullback of the polarization in §3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Whiskering with a line bundle reflects epimorphisms. -/
theorem epi_of_epi_whiskerLeft (L : X.Modules) [L.IsLineBundle]
    {A B : X.Modules} (g : A ⟶ B) (h : Epi (L ◁ g)) : Epi g := by
  obtain ⟨u⟩ := nonempty_tensorObj_dual_iso_tensorUnit L
  let u' : (AlgebraicGeometry.Scheme.Modules.dual L ⊗ L) ≅ 𝟙_ X.Modules := β_ _ _ ≪≫ u
  have h1 : Epi (AlgebraicGeometry.Scheme.Modules.dual L ◁ (L ◁ g)) := epi_whiskerLeft _
  have h2 : Epi ((AlgebraicGeometry.Scheme.Modules.dual L ⊗ L) ◁ g) := by
    rw [MonoidalCategory.tensor_whiskerLeft]
    infer_instance
  have h3 : Epi ((𝟙_ X.Modules) ◁ g) := by
    have hx := MonoidalCategory.whisker_exchange u'.hom g
    have : (𝟙_ X.Modules) ◁ g =
        u'.inv ▷ A ≫ ((AlgebraicGeometry.Scheme.Modules.dual L ⊗ L) ◁ g) ≫ u'.hom ▷ B := by
      rw [hx, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
        MonoidalCategory.id_whiskerRight, Category.id_comp]
    rw [this]
    infer_instance
  rw [MonoidalCategory.id_whiskerLeft] at h3
  have h4 : Epi (g ≫ (λ_ B).inv) := epi_of_epi (λ_ A).hom _
  exact (epi_comp_iff_of_isIso g (λ_ B).inv).mp h4

theorem monoidalPow_isLineBundle' (N : X.Modules) [N.IsLineBundle] (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPow N m).IsLineBundle := by
  induction m with
  | zero => exact inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsLineBundle
  | succ n ih =>
      have := ih
      exact AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.monoidalPow N n) N)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj.LiftData

variable {X T T' : AlgebraicGeometry.Scheme.{u}}
  {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

/-- Transport of Ψ along an equality of degrees. -/
theorem Ψ_eqToHom {a b : ℕ} (h : a = b) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (eqToHom (congrArg S.part h)) ≫ D.Ψ b =
      D.Ψ a ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.monoidalPow M) h) := by
  subst h; simp

theorem epi_map_Ψ_add (g : T' ⟶ T) (a b : ℕ)
    (ha : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ a)))
    (hb : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ b))) :
    Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ (a + b))) := by
  have h := congrArg (AlgebraicGeometry.Scheme.Modules.pullback g).map (D.map_mul a b)
  simp only [Functor.map_comp, Functor.Monoidal.map_tensor] at h
  have : Epi (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := T'.Modules)
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ a))
      ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ b))) :=
    AlgebraicGeometry.Scheme.Modules.epi_tensorHom _ _ ha hb
  have : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (S.mul a b)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ (a + b))) := by
    rw [h]; infer_instance
  exact epi_of_epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (S.mul a b))) _

theorem epi_map_Ψ_mul (g : T' ⟶ T) (n : ℕ)
    (hn : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ n))) (k : ℕ) :
    Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ ((k + 1) * n))) := by
  induction k with
  | zero => rw [Nat.zero_add, Nat.one_mul]; exact hn
  | succ k ih =>
    rw [Nat.succ_mul]
    exact D.epi_map_Ψ_add g _ _ ih hn

/-- Θ_ℓ := f^*(mulPowOne_{S^{(m)}} ℓ) ≫ Ψ_{ℓ m} : f^*(S_m^{⊗ℓ}) ⟶ M^{⊗ℓm}. -/
def powHom (m ℓ : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part (1 * m)) ℓ) ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow M (ℓ * m) :=
  (AlgebraicGeometry.Scheme.Modules.pullback f).map ((S.veronese m).mulPowOne ℓ) ≫ D.Ψ (ℓ * m)

end AlgebraicGeometry.Scheme.relativeProj.LiftData

namespace CategoryTheory

open MonoidalCategory

variable {C D : Type*} [Category C] [Category D]

theorem Functor.epi_map_comp (F : C ⥤ D) {A B E : C} (u : A ⟶ B) (v : B ⟶ E)
    (hu : Epi (F.map u)) (hv : Epi (F.map v)) : Epi (F.map (u ≫ v)) := by
  rw [F.map_comp]; exact epi_comp _ _

variable [MonoidalCategory C] [MonoidalCategory D]

/-- Variable-level identity behind `powHom_succ`. -/
theorem Functor.Monoidal.map_comp_whiskerRight_aux (P : C ⥤ D) [P.Monoidal]
    {Q₀ Q Q' R Z : C} {A B E : D}
    (i : Q₀ ⟶ Q ⊗ R) (θ : Q ⟶ Q') (μ : Q' ⊗ R ⟶ Z) (ψZ : P.obj Z ⟶ E)
    (ψQ : P.obj Q' ⟶ A) (ψR : P.obj R ⟶ B) (c : A ⊗ B ⟶ E)
    (hμ : P.map μ ≫ ψZ = Functor.OplaxMonoidal.δ P Q' R ≫ (ψQ ⊗ₘ ψR) ≫ c) :
    P.map (i ≫ (θ ▷ R) ≫ μ) ≫ ψZ =
      P.map i ≫ Functor.OplaxMonoidal.δ P Q R ≫ ((P.map θ ≫ ψQ) ▷ P.obj R) ≫ (A ◁ ψR) ≫ c := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hμ,
    ← Category.assoc (P.map (θ ▷ R)), ← Functor.OplaxMonoidal.δ_natural_left, Category.assoc,
    MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight, Category.assoc, Category.assoc]

/-- Variable-level epi descent: from `F.map (a ≫ b ≫ θ ▷ N ≫ L ◁ ψ ≫ e)` epi (`e` iso) to
`F.obj L ◁ F.map ψ` epi. -/
theorem Functor.Monoidal.epi_obj_whiskerLeft_map_of_epi_map (F : C ⥤ D) [F.Monoidal]
    {A₀ A₁ A₂ L N N' E : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂ ⊗ N) (θ : A₂ ⟶ L) (ψ : N ⟶ N') (e : L ⊗ N' ⟶ E) [IsIso e]
    (h : Epi (F.map (a ≫ b ≫ (θ ▷ N) ≫ (L ◁ ψ) ≫ e))) : Epi (F.obj L ◁ F.map ψ) := by
  simp only [Functor.map_comp] at h
  have h2 : Epi (F.map b ≫ F.map (θ ▷ N) ≫ F.map (L ◁ ψ) ≫ F.map e) := epi_of_epi (F.map a) _
  have h3 : Epi (F.map (θ ▷ N) ≫ F.map (L ◁ ψ) ≫ F.map e) := epi_of_epi (F.map b) _
  have h4 : Epi (F.map (L ◁ ψ) ≫ F.map e) := epi_of_epi (F.map (θ ▷ N)) _
  rw [epi_comp_iff_of_isIso, Functor.Monoidal.map_whiskerLeft, epi_comp_iff_of_epi,
    epi_comp_iff_of_isIso] at h4
  exact h4

end CategoryTheory

namespace AlgebraicGeometry.Scheme.relativeProj.LiftData

variable {X T T' : AlgebraicGeometry.Scheme.{u}}
  {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

/-- `map_mul` for the Veronese multiplication `S_{ℓm} ⊗ S_{1·m} → S_{(ℓ+1)m}`, written with `δ`. -/
theorem map_veroneseMul_comp_Ψ (m ℓ : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map ((S.veronese m).mul ℓ 1) ≫ D.Ψ ((ℓ + 1) * m) =
      Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback f) (S.part (ℓ * m)) (S.part (1 * m)) ≫
        (D.Ψ (ℓ * m) ⊗ₘ D.Ψ (1 * m)) ≫
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M (ℓ * m) (1 * m)).hom ≫
          eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.monoidalPow M) (add_mul ℓ 1 m).symm)) := by
  show (AlgebraicGeometry.Scheme.Modules.pullback f).map
      (S.mul (ℓ * m) (1 * m) ≫ eqToHom (congrArg S.part (add_mul ℓ 1 m).symm)) ≫ D.Ψ ((ℓ + 1) * m) = _
  rw [Functor.map_comp, Category.assoc, D.Ψ_eqToHom (add_mul ℓ 1 m).symm, ← Category.assoc, D.map_mul,
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_eq_δ]
  simp only [Category.assoc]

theorem powHom_succ (m ℓ : ℕ) :
    D.powHom m (ℓ + 1) =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part (1 * m)) ℓ) (S.part (1 * m))).hom ≫
        Functor.OplaxMonoidal.δ (AlgebraicGeometry.Scheme.Modules.pullback f)
          (AlgebraicGeometry.Scheme.Modules.tensorPow (S.part (1 * m)) ℓ) (S.part (1 * m)) ≫
        (D.powHom m ℓ ▷ (AlgebraicGeometry.Scheme.Modules.pullback f).obj (S.part (1 * m))) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M (ℓ * m) ◁ D.Ψ (1 * m)) ≫
        ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat M (ℓ * m) (1 * m)).hom ≫
          eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.monoidalPow M) (add_mul ℓ 1 m).symm)) :=
  Functor.Monoidal.map_comp_whiskerRight_aux (AlgebraicGeometry.Scheme.Modules.pullback f) _
    ((S.veronese m).mulPowOne ℓ) ((S.veronese m).mul ℓ 1) (D.Ψ ((ℓ + 1) * m)) (D.Ψ (ℓ * m)) (D.Ψ (1 * m)) _
    (D.map_veroneseMul_comp_Ψ m ℓ)

/-- From Ψ_n epi (after pulling back along g) and S^{(m)} generated in degree one, Ψ_m is epi after g. -/
theorem epi_map_Ψ_of_sufficientlyDivisible [M.IsLineBundle] (g : T' ⟶ T) (m : ℕ)
    (hm : S.SufficientlyDivisible m) (n : ℕ) (hn : 0 < n)
    (h : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ n))) :
    Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ m)) := by
  obtain ⟨hm0, hgen⟩ := hm
  have hP : (AlgebraicGeometry.Scheme.Modules.pullback f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f)
  have hF : (AlgebraicGeometry.Scheme.Modules.pullback g).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g)
  have h1 : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map ((S.veronese m).mulPowOne n))) := by
    have := hgen n hn
    infer_instance
  have h2 : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.Ψ (n * m))) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.mul_comm]
    exact D.epi_map_Ψ_mul g n h k
  have hΘ : Epi ((AlgebraicGeometry.Scheme.Modules.pullback g).map (D.powHom m n)) :=
    Functor.epi_map_comp _ _ _ h1 h2
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, n = ℓ + 1 := ⟨n - 1, by omega⟩
  rw [D.powHom_succ] at hΘ
  have h3 := Functor.Monoidal.epi_obj_whiskerLeft_map_of_epi_map
    (AlgebraicGeometry.Scheme.Modules.pullback g) _ _ (D.powHom m ℓ) (D.Ψ (1 * m)) _ hΘ
  have : (AlgebraicGeometry.Scheme.Modules.monoidalPow M (ℓ * m)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.monoidalPow_isLineBundle' M _
  have h5 := AlgebraicGeometry.Scheme.Modules.epi_of_epi_whiskerLeft _ _ h3
  rw [Nat.one_mul] at h5
  exact h5

end AlgebraicGeometry.Scheme.relativeProj.LiftData

/-- (b) For sufficiently divisible `m`, `Ψ_m` is an epimorphism (the step "locally surjective in some positive
degree ⟹ surjective in sufficiently divisible degrees" of Stacks 01O4).

Proof: epimorphisms can be checked on an open cover (`Modules.epi_of_openCover`). For `t ∈ T`, `D.generates t`
gives `U ∋ t` and `n > 0` with `Ψ_n|_U` epi. Write `F = (U.ι)^*`. (1) `epi_map_Ψ_add`: by `D.map_mul` and
"pullback is strong monoidal, tensoring preserves epimorphisms", `F(Ψ_a)`, `F(Ψ_b)` epi ⟹ `F(Ψ_{a+b})` epi; so
`F(Ψ_{kn})` is epi (`epi_map_Ψ_mul`), in particular `F(Ψ_{nm})`. (2) `S^{(m)}` generated in degree one gives
`mulPowOne n : S_m^{⊗n} ↠ S_{nm}` epi, so `Θ_n := f^*(mulPowOne n) ≫ Ψ_{nm}` is epi under `F`. (3) `powHom_succ`:
`Θ_{ℓ+1} = iso ≫ (Θ_ℓ ▷ f^*S_m) ≫ (M^{⊗ℓm} ◁ Ψ_m) ≫ iso`, so `F(M^{⊗ℓm}) ◁ F(Ψ_m)` is epi
(`epi_obj_whiskerLeft_map_of_epi_map`). (4) `F(M^{⊗ℓm})` is a line bundle, and whiskering with a line bundle
reflects epimorphisms (`epi_of_epi_whiskerLeft`), so `F(Ψ_m)` is epi. -/
theorem AlgebraicGeometry.Scheme.relativeProj.LiftData.epi_of_sufficientlyDivisible
    {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (g : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S g M) (m : ℕ)
    (hm : S.SufficientlyDivisible m) :
    CategoryTheory.Epi (D.Ψ m) := by
  choose U hU n hn hepi using D.generates
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, hU t⟩
  refine AlgebraicGeometry.Scheme.Modules.epi_of_openCover _ (T.openCoverOfIsOpenCover U hcov) fun t => ?_
  exact D.epi_map_Ψ_of_sufficientlyDivisible (U t).ι m hm (n t) (hn t) (hepi t)


/-- (a) The input data `Ψ_m` of the lift is induced by the resulting morphism (Stacks 01O4, 01N8: a morphism `r`
to a relative Proj satisfies `r^*O(n) ≅ L^{⊗n}`, and the pullback of the evaluation map `π^*S_n → O(n)` is the
given `Ψ_n`).

**Statement.** τ := `relativeProj.lift S g M D`, `h : τ ≫ π = g`. Then Ψ_m, transported along
`pullbackCongr h : (τ ≫ π)^* ≅ g^*`, is `InducedBy τ`: there is ψ_m : τ^*O(m) ⟶ M^{⊗m} with
Ψ_m ∘ (pullbackCongr h) = (pullbackComp τ π).inv.app (S.part m) ≫ τ^*(evaluation S m) ≫ ψ_m.

**Proof (assembled from the lemmas of `RelativeProjLiftEvaluationTwistFamily.lean`).** With
`α_n := LiftData.evalHom`, `β_n := LiftData.dataHom`,
"twist family" := `LiftData.IsTwistFamilyOn` (a family ψ_n, n ∈ ℕ, satisfying ψ_n ∘ α_n = β_n and multiplicativity
on every open of a given open set):
1. `exists_lift_restrict`: every `t : T` lies in a piece `V' ∋ t` of the definition of `lift`
   (affine, `V' ≤ U ⊓ g⁻¹W`) with `V'.ι ≫ τ = liftLocal S g M D U e W V' hV' hle`.
2. `LiftData.exists_twistFamily_of_piece` (E, Stacks 01O4 (2)): each piece carries a twist
   family — the transport of the canonical family `φ^*O_{Proj A(W)}(n) → O_{V'}`, `a/s^k ↦ Φ(a)Φ(s)^{-k}`, for
   `φ = Proj.fromOfGlobalSections Φ`.
3. `LiftData.twistFamily_sectionMap_unique` (U, 01O4 "up to strict equivalence", 01MN):
   over any open of a piece, two twist families have the same section maps in every degree. Hence the degree-`m`
   members of the families of two pieces agree on the overlap (`IsTwistFamilyOn.mono`) — no chart or
   trivialization is ever compared.
4. Glue the degree-`m` members with `Modules.exists_hom_of_sectionMap_agree` (`ModulesHomGlue.lean`)
   to ψ_m : τ^*O(m) ⟶ M^{⊗m}; `α_m ≫ ψ_m = β_m` is checked on sections, locally on the cover, by (F) of the
   pieces and the naturality of `α_m`, `β_m`, ψ_m. Since `pullbackCongr h = pullbackCongr lift_hom` by proof
   irrelevance, this is the statement.
The route never changes the chart `W`, so no compatibility of `liftLocal` under a change of chart is used here.

**Edge cases.** m = 0: O(0) = O, evaluation is the unit, ψ_0 = D.map_one-transport (fine). T = ∅: vacuous.
M not trivial on any single U: handled by gluing. The statement needs `h` only to transport; it is `lift_hom`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.lift_inducedBy {X T : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (g : T ⟶ X) (M : T.Modules) [M.IsLineBundle]
    (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S g M) (m : ℕ)
    (h : AlgebraicGeometry.Scheme.relativeProj.lift S g M D ≫
      (AlgebraicGeometry.Scheme.relativeProj S).hom = g) :
    AlgebraicGeometry.Scheme.relativeProj.InducedBy (AlgebraicGeometry.Scheme.relativeProj.lift S g M D)
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).hom.app (S.part m) ≫ D.Ψ m) := by
  classical
  -- (1) the cover of T by the pieces of `lift`
  choose U e W V' hV' hle ht hτ using fun t : T =>
    AlgebraicGeometry.Scheme.relativeProj.exists_lift_restrict S g M D t
  -- (2) a twist family on each piece (leaf E)
  choose ψ hψ using fun t : T =>
    D.exists_twistFamily_of_piece (U t) (e t) (W t) (V' t) (hV' t) (hle t) (hτ t)
  have hcov : ⨆ t, V' t = ⊤ := by
    rw [eq_top_iff]
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨t, ht t⟩
  -- (3) the degree-m members agree on overlaps (leaf U)
  have hf : ∀ s t (A : T.Opens) (hs : A ≤ V' s) (ht' : A ≤ V' t),
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ s m) A hs =
        AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ t m) A ht' :=
    fun s t A hs ht' => D.twistFamily_sectionMap_unique (U s) (e s) (W s) (V' s) (hV' s) (hle s) (hτ s) A hs
      (ψ s) (ψ t) hs ht' (AlgebraicGeometry.Scheme.relativeProj.LiftData.IsTwistFamilyOn.mono D (hψ s) hs)
      (AlgebraicGeometry.Scheme.relativeProj.LiftData.IsTwistFamilyOn.mono D (hψ t) ht') m
  -- (4) glue
  obtain ⟨Ψ', hΨ'⟩ := AlgebraicGeometry.Scheme.Modules.exists_hom_of_sectionMap_agree V' hcov _ _
    (fun t => ψ t m) hf
  refine ⟨Ψ', ?_⟩
  -- (5) the factorization holds because it holds on every piece
  have key : D.dataHom m = D.evalHom m ≫ Ψ' := by
    ext A s
    refine TopCat.Sheaf.eq_of_locally_eq'
      ⟨(AlgebraicGeometry.Scheme.Modules.monoidalPow M m).presheaf,
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M m).isSheaf⟩
      (fun t => A ⊓ V' t) A (fun t => homOfLE inf_le_left) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ t, V' t := by rw [hcov]; trivial
      obtain ⟨t, ht'⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, hx, ht'⟩
    · intro t
      have nat1 := fun y => ConcreteCategory.congr_hom
        ((D.dataHom m).mapPresheaf.naturality (homOfLE (inf_le_left : A ⊓ V' t ≤ A)).op) y
      have nat2 := fun y => ConcreteCategory.congr_hom
        ((D.evalHom m).mapPresheaf.naturality (homOfLE (inf_le_left : A ⊓ V' t ≤ A)).op) y
      have nat3 := fun y => ConcreteCategory.congr_hom
        (Ψ'.mapPresheaf.naturality (homOfLE (inf_le_left : A ⊓ V' t ≤ A)).op) y
      simp only [ConcreteCategory.comp_apply, AlgebraicGeometry.Scheme.Modules.mapPresheaf_app] at nat1 nat2 nat3
      change (AlgebraicGeometry.Scheme.Modules.monoidalPow M m).presheaf.map _ ((D.dataHom m).app A s) =
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M m).presheaf.map _ (Ψ'.app A ((D.evalHom m).app A s))
      rw [← nat1, ← nat3, ← nat2, hΨ' t (A ⊓ V' t) inf_le_right, (hψ t).1 m (A ⊓ V' t) inf_le_right]
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.evalHom at key
  rw [Category.assoc] at key
  exact key

end
