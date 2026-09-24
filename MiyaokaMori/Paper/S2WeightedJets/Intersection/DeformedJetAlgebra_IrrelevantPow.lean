import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_EpiTensor
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_WhiskerAdd

/-! # Powers of the irrelevant ideal and their multiplicativity

Powers of the irrelevant ideal `S_+ = ⊕_{j>0} S_j` of a graded quasi-coherent algebra `S` on a scheme `X`,
degree by degree, as image subobjects `I^{(p)}_j ⊆ S_j` (`irrelevantPow`), and the multiplicativity
`S_+^{(a)} · S_+^{(b)} ⊆ S_+^{(a+b)}` (`irrelevantPow_mul_condition`).

**Proof architecture.** `S.LandsIn f p` means `f ≫ cokernel.π (I^{(p)}_n → S_n) = 0`, i.e. `f : A ⟶ S_n` factors through
`I^{(p)}_n` (`Abelian.monoLift`). The closure lemmas (`landsIn_comp`, `landsIn_of_epi`, `landsIn_biproduct`,
`landsIn_of_whiskerLeft_biproduct`, `landsIn_of_whiskerRight_biproduct`, `landsIn_eqToHom`) reduce every statement to
the components of the generating map `irrelevantPow.gen`, whose components land in `I^{(p+1)}` by construction
(`landsIn_gen_component`). Then:
* `landsIn_whiskerLeft_mul_succ`: `d ≥ 1`, `f` lands in `I^{(p)}_m` ⇒ `S_d · f` lands in `I^{(p+1)}_{d+m}` (a component of `gen`);
* `landsIn_whiskerLeft_mul`: `f` lands in `I^{(p)}_m` ⇒ `S_d · f` lands in `I^{(p)}_{d+m}` (induction on `p`; the step
  uses the identity `d·(e·x) = e·(d·x)` in `S`, `whiskerLeft_gen_component_comp_mul`, from `mul_assoc` and `mul_comm`);
* `landsIn_tensor_mul`: `f` lands in `I^{(a)}_m`, `g` in `I^{(b)}_n` ⇒ `f·g` lands in `I^{(a+b)}_{m+n}` (induction on `a`;
  the step uses `(e·x)·y = e·(x·y)`, `gen_component_tensorHom_comp_mul`, from `mul_assoc`).

Source: Stacks 052P (extended Rees algebra), basic property `S_+^a · S_+^b ⊆ S_+^{a+b}` of ideal powers; used for
the Rees deformation of Lemma 2.3 of the paper. Edge cases: `I^{(0)}_j = S_j` with inclusion `𝟙` (its cokernel is `0`); `p > j` gives the
image of an empty biproduct, i.e. `0`, and every statement is trivially true.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The degree-`j` piece `I^{(p)}_j` of the `p`-th power of the irrelevant ideal `S_+ = ⊕_{j>0} S_j`, as an
image subobject of `S_j` (an object together with a monomorphism into `S_j`):
`I^{(0)}_j = S_j`; `I^{(p+1)}_j = Im(⊕_{a=1}^{j} S_a ⊗ I^{(p)}_{j-a} → S_a ⊗ S_{j-a} → S_j)` (multiplication;
`a ≥ 1` keeps the factor in `S_+`). -/

noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) : ℕ → ∀ j : ℕ, Σ M : X.Modules, (M ⟶ S.part j)
  | 0, j => ⟨S.part j, CategoryTheory.CategoryStruct.id _⟩
  | p + 1, j =>
    let f : CategoryTheory.Limits.biproduct
        (fun a : Fin j => S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1) ⟶ S.part j :=
      CategoryTheory.Limits.biproduct.desc fun a =>
        (S.part (a.1 + 1) ◁ (S.irrelevantPow p (j - (a.1 + 1))).2) ≫ S.mul _ _ ≫
          CategoryTheory.eqToHom (congrArg S.part (by have := a.2; omega))
    ⟨CategoryTheory.Limits.image f, CategoryTheory.Limits.image.ι f⟩

/-- The first defining equation: `S_+^{(0)}_j = S_j` (with the identity inclusion). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow_zero {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (j : ℕ) :
    S.irrelevantPow 0 j = ⟨S.part j, CategoryTheory.CategoryStruct.id _⟩ := rfl

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The generating map `⊕_{c : Fin n} S_{c+1} ⊗ I^{(p)}_{n-c-1} → S_n` of `I^{(p+1)}_n` (the `let f` in `irrelevantPow`). -/
noncomputable def irrelevantPow.gen (p n : ℕ) :
    CategoryTheory.Limits.biproduct
        (fun a : Fin n => S.part (a.1 + 1) ⊗ (S.irrelevantPow p (n - (a.1 + 1))).1) ⟶ S.part n :=
  CategoryTheory.Limits.biproduct.desc fun a =>
    (S.part (a.1 + 1) ◁ (S.irrelevantPow p (n - (a.1 + 1))).2) ≫ S.mul _ _ ≫
      CategoryTheory.eqToHom (congrArg S.part (by have := a.2; omega))

/-- The second defining equation: `I^{(p+1)}_n = Im (irrelevantPow.gen S p n)` with its image inclusion. -/
theorem irrelevantPow_succ (p n : ℕ) :
    S.irrelevantPow (p + 1) n = ⟨CategoryTheory.Limits.image (irrelevantPow.gen S p n),
      CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)⟩ := rfl

/-- The inclusion `I^{(p)}_n → S_n` is a monomorphism (`𝟙` for `p = 0`, an image inclusion for `p + 1`). -/
theorem mono_irrelevantPow (p n : ℕ) : Mono (S.irrelevantPow p n).2 := by
  cases p with
  | zero => exact (inferInstance : Mono (CategoryTheory.CategoryStruct.id (S.part n)))
  | succ p => exact (inferInstance : Mono (CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)))

/-- `f : A ⟶ S_n` lands in `I^{(p)}_n`: its composite with the cokernel projection of the inclusion vanishes. -/
def LandsIn {A : X.Modules} {n : ℕ} (f : A ⟶ S.part n) (p : ℕ) : Prop :=
  f ≫ CategoryTheory.Limits.cokernel.π (S.irrelevantPow p n).2 = 0

theorem landsIn_zero {A : X.Modules} {n : ℕ} (f : A ⟶ S.part n) : S.LandsIn f 0 := by
  show f ≫ CategoryTheory.Limits.cokernel.π (CategoryTheory.CategoryStruct.id (S.part n)) = 0
  rw [CategoryTheory.Limits.cokernel.π_of_epi, comp_zero]

theorem landsIn_self (p n : ℕ) : S.LandsIn (S.irrelevantPow p n).2 p :=
  CategoryTheory.Limits.cokernel.condition _

theorem landsIn_comp {A B : X.Modules} {n : ℕ} {f : B ⟶ S.part n} {p : ℕ} (g : A ⟶ B) (h : S.LandsIn f p) :
    S.LandsIn (g ≫ f) p := by
  unfold LandsIn at *
  rw [Category.assoc, h, comp_zero]

theorem landsIn_of_epi {A B : X.Modules} {n : ℕ} {f : B ⟶ S.part n} {p : ℕ} (e : A ⟶ B) [Epi e]
    (h : S.LandsIn (e ≫ f) p) : S.LandsIn f p := by
  unfold LandsIn at *
  rw [Category.assoc] at h
  exact (cancel_epi e).1 (by rw [h, comp_zero])

/-- A morphism landing in `I^{(p)}_n` factors through it (`Abelian.monoLift`). -/
theorem landsIn_iff_exists {A : X.Modules} {n : ℕ} (f : A ⟶ S.part n) (p : ℕ) :
    S.LandsIn f p ↔ ∃ g : A ⟶ (S.irrelevantPow p n).1, f = g ≫ (S.irrelevantPow p n).2 := by
  haveI := S.mono_irrelevantPow p n
  constructor
  · intro h
    exact ⟨CategoryTheory.Abelian.monoLift _ f h, (CategoryTheory.Abelian.monoLift_comp _ f h).symm⟩
  · rintro ⟨g, rfl⟩
    exact S.landsIn_comp g (S.landsIn_self p n)

theorem landsIn_congr_p {A : X.Modules} {n : ℕ} {f : A ⟶ S.part n} {p p' : ℕ} (h : p = p')
    (hf : S.LandsIn f p) : S.LandsIn f p' := by
  subst h; exact hf

theorem landsIn_eqToHom {A : X.Modules} {n n' : ℕ} {f : A ⟶ S.part n} {p : ℕ} (h : n = n')
    (hf : S.LandsIn f p) : S.LandsIn (f ≫ eqToHom (congrArg S.part h)) p := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  exact hf

theorem landsIn_comp_eqToHom {A B : X.Modules} {n n' : ℕ} {f : A ⟶ B} {g : B ⟶ S.part n} {p : ℕ} (h : n = n')
    (hf : S.LandsIn (f ≫ g) p) : S.LandsIn (f ≫ g ≫ eqToHom (congrArg S.part h)) p := by
  rw [← Category.assoc]
  exact S.landsIn_eqToHom h hf

theorem landsIn_biproduct {J : Type} [Fintype J] (F : J → X.Modules) {n p : ℕ}
    (f : CategoryTheory.Limits.biproduct F ⟶ S.part n)
    (h : ∀ j, S.LandsIn (CategoryTheory.Limits.biproduct.ι F j ≫ f) p) : S.LandsIn f p := by
  unfold LandsIn at *
  apply CategoryTheory.Limits.biproduct.hom_ext'
  intro j
  rw [comp_zero, ← Category.assoc, h j]

theorem landsIn_of_whiskerRight_biproduct {J : Type} [Fintype J] (F : J → X.Modules) (N : X.Modules) {n p : ℕ}
    (f : CategoryTheory.Limits.biproduct F ⊗ N ⟶ S.part n)
    (h : ∀ j, S.LandsIn ((CategoryTheory.Limits.biproduct.ι F j ▷ N) ≫ f) p) : S.LandsIn f p := by
  unfold LandsIn at *
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerRight_hom_ext F N _ 0
  intro j
  rw [comp_zero, ← Category.assoc, h j]

theorem landsIn_of_whiskerLeft_biproduct {J : Type} [Fintype J] (N : X.Modules) (F : J → X.Modules) {n p : ℕ}
    (f : N ⊗ CategoryTheory.Limits.biproduct F ⟶ S.part n)
    (h : ∀ j, S.LandsIn ((N ◁ CategoryTheory.Limits.biproduct.ι F j) ≫ f) p) : S.LandsIn f p := by
  unfold LandsIn at *
  apply AlgebraicGeometry.Scheme.Modules.biproduct_whiskerLeft_hom_ext N F _ 0
  intro j
  rw [comp_zero, ← Category.assoc, h j]

/-- Each component of the generating map lands in `I^{(p+1)}_n`. -/
theorem landsIn_gen_component (p n : ℕ) (c : Fin n) :
    S.LandsIn (CategoryTheory.Limits.biproduct.ι _ c ≫ irrelevantPow.gen S p n) (p + 1) := by
  show (CategoryTheory.Limits.biproduct.ι _ c ≫ irrelevantPow.gen S p n) ≫
    CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)) = 0
  have h0 : irrelevantPow.gen S p n ≫
      CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)) = 0 := by
    calc irrelevantPow.gen S p n ≫
          CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)) =
        (CategoryTheory.Limits.factorThruImage (irrelevantPow.gen S p n) ≫
          CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)) ≫
          CategoryTheory.Limits.cokernel.π (CategoryTheory.Limits.image.ι (irrelevantPow.gen S p n)) := by
            rw [CategoryTheory.Limits.image.fac]
      _ = 0 := by rw [Category.assoc, CategoryTheory.Limits.cokernel.condition, comp_zero]
  rw [Category.assoc, h0, comp_zero]

theorem ι_gen (p n : ℕ) (c : Fin n) :
    CategoryTheory.Limits.biproduct.ι _ c ≫ irrelevantPow.gen S p n =
      (S.part (c.1 + 1) ◁ (S.irrelevantPow p (n - (c.1 + 1))).2) ≫ S.mul _ _ ≫
        CategoryTheory.eqToHom (congrArg S.part (by have := c.2; omega)) := by
  unfold irrelevantPow.gen
  rw [CategoryTheory.Limits.biproduct.ι_desc]

/-- Index transport for `S_d · I^{(p)}_m ⊆ I^{(q)}_n` statements. -/
theorem landsIn_whiskerLeft_mul_transport {d d' m m' n p q : ℕ} (hd : d' = d) (hm : m' = m)
    (hn : d + m = n) (hn' : d' + m' = n)
    (h : S.LandsIn ((S.part d' ◁ (S.irrelevantPow p m').2) ≫ S.mul d' m' ≫ eqToHom (congrArg S.part hn')) q) :
    S.LandsIn ((S.part d ◁ (S.irrelevantPow p m).2) ≫ S.mul d m ≫ eqToHom (congrArg S.part hn)) q := by
  subst hd; subst hm; exact h

/-- `S_d · I^{(p)}_m ⊆ I^{(p+1)}_{d+m}` for `d ≥ 1`: it is the component `d - 1` of the generating map. -/
theorem landsIn_whiskerLeft_irrelevantPow_mul_succ (p d m n : ℕ) (hd : 0 < d) (hn : d + m = n) :
    S.LandsIn ((S.part d ◁ (S.irrelevantPow p m).2) ≫ S.mul d m ≫ eqToHom (congrArg S.part hn)) (p + 1) := by
  have hc : d - 1 < n := by omega
  have h := S.landsIn_gen_component p n ⟨d - 1, hc⟩
  rw [S.ι_gen p n ⟨d - 1, hc⟩] at h
  exact S.landsIn_whiskerLeft_mul_transport (by dsimp only [Fin.val_mk]; omega)
    (by dsimp only [Fin.val_mk]; omega) hn (by dsimp only [Fin.val_mk]; omega) h

/-- `d ≥ 1`, `f` lands in `I^{(p)}_m` ⇒ `S_d · f` lands in `I^{(p+1)}_{d+m}`. -/
theorem landsIn_whiskerLeft_mul_succ {A : X.Modules} {m p : ℕ} {f : A ⟶ S.part m} (hf : S.LandsIn f p)
    (d : ℕ) (hd : 0 < d) : S.LandsIn ((S.part d ◁ f) ≫ S.mul d m) (p + 1) := by
  obtain ⟨g, rfl⟩ := (S.landsIn_iff_exists f p).1 hf
  rw [CategoryTheory.MonoidalCategory.whiskerLeft_comp, Category.assoc]
  apply S.landsIn_comp
  have h := S.landsIn_whiskerLeft_irrelevantPow_mul_succ p d m (d + m) hd rfl
  rw [eqToHom_refl, Category.comp_id] at h
  exact h

/-- `(S.part d ◁ eqToHom) ≫ mul = mul ≫ eqToHom`. -/
@[reassoc]
theorem whiskerLeft_eqToHom_comp_mul (d : ℕ) {n n' : ℕ} (h : n = n') :
    (S.part d ◁ eqToHom (congrArg S.part h)) ≫ S.mul d n' =
      S.mul d n ≫ eqToHom (congrArg S.part (by rw [h])) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, CategoryTheory.MonoidalCategory.whiskerLeft_id, Category.id_comp,
    Category.comp_id]

/-- `(eqToHom ▷ S.part n) ≫ mul = mul ≫ eqToHom`. -/
@[reassoc]
theorem eqToHom_whiskerRight_comp_mul {m m' : ℕ} (h : m = m') (n : ℕ) :
    (eqToHom (congrArg S.part h) ▷ S.part n) ≫ S.mul m' n =
      S.mul m n ≫ eqToHom (congrArg S.part (by rw [h])) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, CategoryTheory.MonoidalCategory.id_whiskerRight, Category.id_comp,
    Category.comp_id]

/-- `mul e d ▷ S_m' ≫ mul (e+d) m' = α ≫ (S_e ◁ mul d m') ≫ mul e (d+m') ≫ eqToHom` (`mul_assoc` reversed). -/
@[reassoc]
theorem whiskerRight_mul_comp_mul (e d m : ℕ) :
    (S.mul e d ▷ S.part m) ≫ S.mul (e + d) m =
      (α_ (S.part e) (S.part d) (S.part m)).hom ≫ (S.part e ◁ S.mul d m) ≫ S.mul e (d + m) ≫
        eqToHom (congrArg S.part (Nat.add_assoc e d m).symm) := by
  apply (cancel_mono (eqToHom (congrArg S.part (Nat.add_assoc e d m)))).1
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact (S.mul_assoc e d m).symm

/-- `mul d e = β ≫ mul e d ≫ eqToHom` (`mul_comm` reversed). -/
theorem mul_eq_braiding_comp_mul (d e : ℕ) :
    S.mul d e = (β_ (S.part d) (S.part e)).hom ≫ S.mul e d ≫ eqToHom (congrArg S.part (Nat.add_comm e d)) := by
  rw [← Category.assoc, S.mul_comm d e, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The identity `d · (e · x) = e · (d · x)` in `S`, in the shape of a component of `irrelevantPow.gen`. -/
theorem whiskerLeft_gen_component_comp_mul (d e : ℕ) {A : X.Modules} {m' m : ℕ} (u : A ⟶ S.part m')
    (h : e + m' = m) :
    (S.part d ◁ ((S.part e ◁ u) ≫ S.mul e m' ≫ eqToHom (congrArg S.part h))) ≫ S.mul d m =
      (α_ (S.part d) (S.part e) A).inv ≫ ((β_ (S.part d) (S.part e)).hom ▷ A) ≫
        (α_ (S.part e) (S.part d) A).hom ≫ (S.part e ◁ ((S.part d ◁ u) ≫ S.mul d m')) ≫ S.mul e (d + m') ≫
        eqToHom (congrArg S.part (by omega)) := by
  subst h
  simp only [CategoryTheory.MonoidalCategory.whiskerLeft_comp, Category.assoc, eqToHom_refl,
    Category.comp_id]
  have h1 : (S.part d ◁ S.mul e m') ≫ S.mul d (e + m') =
      (α_ (S.part d) (S.part e) (S.part m')).inv ≫ (S.mul d e ▷ S.part m') ≫ S.mul (d + e) m' ≫
        eqToHom (congrArg S.part (Nat.add_assoc d e m')) := by
    rw [← S.mul_assoc, Iso.inv_hom_id_assoc]
  rw [h1, S.mul_eq_braiding_comp_mul d e, CategoryTheory.MonoidalCategory.comp_whiskerRight,
    CategoryTheory.MonoidalCategory.comp_whiskerRight, Category.assoc, Category.assoc,
    S.eqToHom_whiskerRight_comp_mul_assoc (Nat.add_comm e d) m', S.whiskerRight_mul_comp_mul_assoc e d m']
  simp only [eqToHom_trans]
  rw [CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc,
    CategoryTheory.MonoidalCategory.whisker_exchange_assoc,
    CategoryTheory.MonoidalCategory.associator_naturality_right_assoc]

/-- `f` lands in `I^{(p)}_m` ⇒ `S_d · f` lands in `I^{(p)}_{d+m}` (any `d`), by induction on `p`. -/
theorem landsIn_whiskerLeft_mul (p : ℕ) : ∀ {A : X.Modules} {m : ℕ} {f : A ⟶ S.part m}, S.LandsIn f p →
    ∀ d : ℕ, S.LandsIn ((S.part d ◁ f) ≫ S.mul d m) p := by
  induction p with
  | zero => intros; exact S.landsIn_zero _
  | succ p ih =>
    intro A m f hf d
    obtain ⟨g, rfl⟩ := (S.landsIn_iff_exists f (p + 1)).1 hf
    rw [CategoryTheory.MonoidalCategory.whiskerLeft_comp, Category.assoc]
    apply S.landsIn_comp
    show S.LandsIn ((S.part d ◁ CategoryTheory.Limits.image.ι (irrelevantPow.gen S p m)) ≫ S.mul d m) (p + 1)
    have : Epi (S.part d ◁ CategoryTheory.Limits.factorThruImage (irrelevantPow.gen S p m)) :=
      AlgebraicGeometry.Scheme.Modules.epi_whiskerLeft _
    apply S.landsIn_of_epi (S.part d ◁ CategoryTheory.Limits.factorThruImage (irrelevantPow.gen S p m))
    rw [← Category.assoc, ← CategoryTheory.MonoidalCategory.whiskerLeft_comp,
      CategoryTheory.Limits.image.fac]
    apply S.landsIn_of_whiskerLeft_biproduct
    intro c
    rw [← Category.assoc, ← CategoryTheory.MonoidalCategory.whiskerLeft_comp, S.ι_gen p m c,
      S.whiskerLeft_gen_component_comp_mul d (c.1 + 1) (S.irrelevantPow p (m - (c.1 + 1))).2
        (by have := c.2; omega)]
    apply S.landsIn_comp
    apply S.landsIn_comp
    apply S.landsIn_comp
    apply S.landsIn_comp_eqToHom (by have := c.2; omega)
    exact S.landsIn_whiskerLeft_mul_succ (ih (S.landsIn_self p _) d) (c.1 + 1) (Nat.succ_pos _)

/-- The identity `(e · x) · y = e · (x · y)` in `S`, in the shape of a component of `irrelevantPow.gen`. -/
theorem gen_component_tensorHom_comp_mul (e : ℕ) {A B : X.Modules} {m' m n : ℕ} (u : A ⟶ S.part m')
    (g : B ⟶ S.part n) (h : e + m' = m) :
    (((S.part e ◁ u) ≫ S.mul e m' ≫ eqToHom (congrArg S.part h)) ⊗ₘ g) ≫ S.mul m n =
      (α_ (S.part e) A B).hom ≫ (S.part e ◁ ((u ⊗ₘ g) ≫ S.mul m' n)) ≫ S.mul e (m' + n) ≫
        eqToHom (congrArg S.part (by omega)) := by
  subst h
  rw [eqToHom_refl, Category.comp_id]
  rw [CategoryTheory.MonoidalCategory.tensorHom_def, CategoryTheory.MonoidalCategory.comp_whiskerRight,
    Category.assoc, Category.assoc, ← CategoryTheory.MonoidalCategory.whisker_exchange_assoc,
    S.whiskerRight_mul_comp_mul e m' n, ← CategoryTheory.MonoidalCategory.tensorHom_def_assoc,
    ← CategoryTheory.MonoidalCategory.id_tensorHom,
    CategoryTheory.MonoidalCategory.associator_naturality_assoc,
    CategoryTheory.MonoidalCategory.id_tensorHom, ← CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc]

/-- `f` lands in `I^{(a)}_m`, `g` in `I^{(b)}_n` ⇒ `f · g` lands in `I^{(a+b)}_{m+n}`, by induction on `a`. -/
theorem landsIn_tensor_mul (a : ℕ) : ∀ {A B : X.Modules} {m n b : ℕ} {f : A ⟶ S.part m} {g : B ⟶ S.part n},
    S.LandsIn f a → S.LandsIn g b → S.LandsIn ((f ⊗ₘ g) ≫ S.mul m n) (a + b) := by
  induction a with
  | zero =>
    intro A B m n b f g _ hg
    apply S.landsIn_congr_p (Nat.zero_add b).symm
    rw [CategoryTheory.MonoidalCategory.tensorHom_def, Category.assoc]
    exact S.landsIn_comp _ (S.landsIn_whiskerLeft_mul b hg m)
  | succ a ih =>
    intro A B m n b f g hf hg
    obtain ⟨ψ, rfl⟩ := (S.landsIn_iff_exists f (a + 1)).1 hf
    rw [← CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom, Category.assoc]
    apply S.landsIn_comp
    show S.LandsIn ((CategoryTheory.Limits.image.ι (irrelevantPow.gen S a m) ⊗ₘ g) ≫ S.mul m n) (a + 1 + b)
    have : Epi (CategoryTheory.Limits.factorThruImage (irrelevantPow.gen S a m) ▷ B) :=
      AlgebraicGeometry.Scheme.Modules.epi_whiskerRight _
    apply S.landsIn_of_epi (CategoryTheory.Limits.factorThruImage (irrelevantPow.gen S a m) ▷ B)
    rw [← Category.assoc, CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom,
      CategoryTheory.Limits.image.fac]
    apply S.landsIn_of_whiskerRight_biproduct
    intro c
    rw [← Category.assoc, CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom, S.ι_gen a m c,
      S.gen_component_tensorHom_comp_mul (c.1 + 1) (S.irrelevantPow a (m - (c.1 + 1))).2 g
        (by have := c.2; omega)]
    apply S.landsIn_comp
    apply S.landsIn_comp_eqToHom (by have := c.2; omega)
    apply S.landsIn_congr_p (show a + b + 1 = a + 1 + b by omega)
    exact S.landsIn_whiskerLeft_mul_succ (ih (S.landsIn_self a _) hg) (c.1 + 1) (Nat.succ_pos _)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- Multiplicativity of the powers of the irrelevant ideal, `S_+^{(a)} · S_+^{(b)} ⊆ S_+^{(a+b)}`, degree by
degree: `I^{(a)}_j ⊗ I^{(b)}_k → S_j ⊗ S_k → S_{j+k}` lands in `I^{(a+b)}_{j+k}` (the composite to the cokernel
is `0`). Source: Stacks 052P (extended Rees algebra) and the basic property `S_+^a · S_+^b = S_+^{a+b}` of ideal
powers. Proof: `landsIn_tensor_mul` applied to the two inclusions (`landsIn_self`). -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.irrelevantPow_mul_condition {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b j k : ℕ) :
    (((S.irrelevantPow a j).2 ⊗ₘ (S.irrelevantPow b k).2) ≫ S.mul j k) ≫
      CategoryTheory.Limits.cokernel.π (S.irrelevantPow (a + b) (j + k)).2 = 0 :=
  S.landsIn_tensor_mul a (S.landsIn_self a j) (S.landsIn_self b k)

end
