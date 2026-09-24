import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcLocalizedModule
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ce01id

/-! # Sections of a tensor product on an affine open

**Stacks 01I8 for tensor products**: for quasi-coherent `A, B` on `X` and an affine open `U`, the section pairing
`tensorSectionsHom A B : Γ(U, A) ⊗_{Γ(U)} Γ(U, B) → Γ(U, A ⊗ B)` is bijective.

Used for `Γ(U, Sym^e F) = Sym^e Γ(U, F)`, which goes through `Γ(U, F^{⊗e}) = Γ(U, F)^{⊗e}`.
See the docstrings below for the route.
Source: Stacks 01I8 (quasi-coherent modules on an affine scheme are determined by global sections), 01CA
(the tensor product of sheaves of modules is the sheafification of the presheaf tensor product).

## Route

1. `bijective_app_of_isAffineOpen_of_locallyBijective` (general): `P` a presheaf of `O_X`-modules, `S` a
   quasi-coherent `O_X`-module, `η : P ⟶ G S` locally injective and locally surjective. If, on the affine open
   `U`, `P` "localizes on basic opens" — (h1) a section of `P(U)` that dies on `D(f)` is killed by a power of
   `f`; (h2) a section of `P(D f)` becomes the restriction of a section of `P(U)` after multiplying by a power
   of `f` — then `η_U : P(U) → S(U)` is bijective. Both halves reduce to "an ideal of `Γ(U)` containing a power
   of `f_x` with `x ∈ D(f_x)` for every `x ∈ U` is the unit ideal" (`QcAffineLocalAux.ideal_eq_top`):
   * injectivity: the annihilator ideal of `p` (with `η p = 0`) is `⊤`, using (h1);
   * surjectivity: for `t ∈ S(U)`, the ideal `{r | r • t ∈ im η_U}` is `⊤`: locally `t|_{D f} = η(q)`, by (h2)
     `f^n q = a|_{D f}`, so `(η a - f^n t)|_{D f} = 0`, and since `S` is quasi-coherent
     `f^k (η a - f^n t) = 0`, i.e. `f^{n+k} t = η (f^k a)`.
   (No gluing inside `P` is needed.)
2. `TensorLocAux`: for `P = G A ⊗ G B` (presheaf tensor product, `P(V) = Γ(V, A) ⊗_{Γ(V)} Γ(V, B)`), the
   restriction `P(U) → P(D f)` is the localization at `f` (Mathlib: `IsLocalizedModule` for
   `TensorProduct.map`, `IsLocalization.moduleTensorEquiv` to change the base ring `Γ(U) → Γ(D f)`;
   `Modules.isLocalizedModule_basicOpen` for `A`, `B`), which gives (h1), (h2).
3. `tensorSectionsHom A B = unit ≫ G(sheafifyTensorTo A B)` (`Adjunction.homEquiv`), the unit
   `P → G(L P)` is locally bijective (Mathlib `toSheafify`), `L P ≅ A ⊗ B` is quasi-coherent
   (`isQuasicoherent_tensor`), and `sheafifyTensorTo` is an isomorphism.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Local-to-global for a locally bijective map from a presheaf that localizes on basic opens.**
`P` a presheaf of `O_X`-modules, `S` a quasi-coherent `O_X`-module, `η : P ⟶ G S` locally injective and
locally surjective (for the topology of `X`). If on the affine open `U`
(h1) `p ∈ P(U)`, `p|_{D f} = 0` implies `f^n p = 0` for some `n`, and
(h2) every `q ∈ P(D f)` satisfies `f^n q = a|_{D f}` for some `n` and `a ∈ P(U)`,
then `η_U : P(U) → S(U)` is bijective.

Proof (Stacks 01I8-style, self-contained). Injectivity: let `η_U p = 0`. Local injectivity gives a covering
sieve on which `p` restricts to `0`; every `x ∈ U` lies in a basic open `D(f_x)` inside a member of the sieve,
so `p|_{D f_x} = 0` and by (h1) `f_x^{n_x} ∈ Ann(p)`. The ideal `Ann(p)` of `Γ(U)` therefore contains, for each
`x ∈ U`, a power of an `f_x` with `x ∈ D(f_x)`, hence is `⊤` (`QcAffineLocalAux.ideal_eq_top`), so `1 • p = 0`.
Surjectivity: let `t ∈ S(U)`, `J := {r ∈ Γ(U) | r • t ∈ im η_U}` (an ideal). Local surjectivity gives, for each
`x ∈ U`, a basic open `D(f) ∋ x` and `q ∈ P(D f)` with `η q = t|_{D f}`. By (h2) `f^n q = a|_{D f}` with
`a ∈ P(U)`; by naturality `(η_U a)|_{D f} = η(a|_{D f}) = f^n η q = (f^n t)|_{D f}`, so `η_U a - f^n t` dies on
`D(f)`; `S` being quasi-coherent, `f^k (η_U a - f^n t) = 0` (`exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`),
i.e. `f^{k+n} t = η_U (f^k a)`, so `f^{k+n} ∈ J`. Hence `J = ⊤`, `1 ∈ J`, and `t ∈ im η_U`. -/
theorem bijective_app_of_isAffineOpen_of_locallyBijective
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (S : X.Modules) [S.IsQuasicoherent]
    (η : P ⟶ (shG X).obj S)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf _).map η)]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf _).map η)]
    {U : X.Opens} (hU : IsAffineOpen U)
    (h1 : ∀ (f : X.ringCatSheaf.obj.obj (op U)) (p : P.obj (op U)),
      P.map (homOfLE (X.basicOpen_le f)).op p = 0 → ∃ n : ℕ, f ^ n • p = 0)
    (h2 : ∀ (f : X.ringCatSheaf.obj.obj (op U)) (q : P.obj (op (X.basicOpen f))),
      ∃ (n : ℕ) (a : P.obj (op U)), P.map (homOfLE (X.basicOpen_le f)).op a =
        (X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op f) ^ n • q) :
    Function.Bijective (η.app (op U)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun p hp => ?_
    have hS : Presheaf.equalizerSieve (F := (_root_.PresheafOfModules.toPresheaf _).obj P)
        (X := op U) p 0 ∈ Opens.grothendieckTopology X U :=
      Presheaf.equalizerSieve_mem _ ((_root_.PresheafOfModules.toPresheaf _).map η) p 0 (by
        change η.app (op U) p = η.app (op U) 0
        rw [map_zero]; exact hp)
    have hI : Ideal.torsionOf (X.ringCatSheaf.obj.obj (op U)) (P.obj (op U)) p = ⊤ := by
      refine QcAffineLocalAux.ideal_eq_top hU _ fun x hx => ?_
      obtain ⟨V, i, hi, hxV⟩ := hS x hx
      obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
      have h0 : P.map (homOfLE (X.basicOpen_le f)).op p = 0 := by
        rw [P.congr_map_apply (f := (homOfLE (X.basicOpen_le f)).op) (g := (homOfLE hfV ≫ i).op)
          (by rfl), op_comp, P.map_comp_apply]
        have hi' : P.map i.op p = P.map i.op 0 := hi
        rw [hi']
        exact (congrArg _ (map_zero _)).trans (map_zero _)
      obtain ⟨n, hn⟩ := h1 f p h0
      exact ⟨f, n, hxf, (Ideal.mem_torsionOf_iff (R := X.ringCatSheaf.obj.obj (op U)) p (f ^ n)).2 hn⟩
    have h1p : (1 : X.ringCatSheaf.obj.obj (op U)) ∈
        Ideal.torsionOf (X.ringCatSheaf.obj.obj (op U)) (P.obj (op U)) p := hI ▸ Submodule.mem_top
    have := (Ideal.mem_torsionOf_iff _ _).1 h1p
    rwa [one_smul] at this
  · intro t
    have hS : Presheaf.imageSieve ((_root_.PresheafOfModules.toPresheaf _).map η) t ∈
        Opens.grothendieckTopology X U :=
      Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
        ((_root_.PresheafOfModules.toPresheaf _).map η) (U := op U) t
    let J : Ideal (X.ringCatSheaf.obj.obj (op U)) :=
      { carrier := {r | ∃ a : P.obj (op U), η.app (op U) a = r • t}
        add_mem' := by
          rintro r s ⟨a, ha⟩ ⟨b, hb⟩
          exact ⟨a + b, by rw [map_add, ha, hb, add_smul]⟩
        zero_mem' := ⟨0, by rw [map_zero, zero_smul]⟩
        smul_mem' := by
          rintro c r ⟨a, ha⟩
          exact ⟨c • a, by rw [_root_.map_smul, ha, smul_smul, smul_eq_mul]⟩ }
    have hJ : J = ⊤ := by
      refine QcAffineLocalAux.ideal_eq_top hU J fun x hx => ?_
      obtain ⟨V, i, hi, hxV⟩ := hS x hx
      obtain ⟨f, hfV, hxf⟩ : ∃ f : X.ringCatSheaf.obj.obj (op U),
          X.basicOpen f ≤ V ∧ x ∈ X.basicOpen f := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
      obtain ⟨q, hq⟩ := hi
      have hq0 : η.app (op V) q = ((shG X).obj S).map i.op t := hq
      -- `q ∈ P(V)` with `η q = t|_V`; restrict to `D(f)`
      let q' : P.obj (op (X.basicOpen f)) := P.map (homOfLE hfV).op q
      have hq' : η.app (op (X.basicOpen f)) q' =
          ((shG X).obj S).map (homOfLE (X.basicOpen_le f)).op t := by
        have hnat := congr_arg (fun k => k q) (η.naturality (homOfLE hfV).op)
        change η.app (op (X.basicOpen f)) (P.map (homOfLE hfV).op q) =
          ((shG X).obj S).map (homOfLE hfV).op (η.app (op V) q) at hnat
        rw [hnat, hq0]
        change ((shG X).obj S).map (homOfLE hfV).op (((shG X).obj S).map i.op t) = _
        rw [← ((shG X).obj S).map_comp_apply, ← op_comp]
        exact (((shG X).obj S).congr_map_apply (by rfl) t)
      obtain ⟨n, a, ha⟩ := h2 f q'
      -- `(η a)|_{D f} = (f^n t)|_{D f}`
      have hres : ((shG X).obj S).map (homOfLE (X.basicOpen_le f)).op
          (η.app (op U) a - f ^ n • t) = 0 := by
        rw [map_sub, ((shG X).obj S).map_smul, ← hq', map_pow]
        have hnat := congr_arg (fun k => k a) (η.naturality (homOfLE (X.basicOpen_le f)).op)
        change η.app (op (X.basicOpen f)) (P.map (homOfLE (X.basicOpen_le f)).op a) =
          ((shG X).obj S).map (homOfLE (X.basicOpen_le f)).op (η.app (op U) a) at hnat
        rw [← hnat, ha, _root_.map_smul]
        exact sub_eq_zero.2 rfl
      obtain ⟨k, hk⟩ :=
        Scheme.Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero S hU f _ hres
      refine ⟨f, k + n, hxf, f ^ k • a, ?_⟩
      have hk' : f ^ k • (η.app (op U) a - f ^ n • t) = 0 := hk
      rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hk'
      rw [_root_.map_smul, hk']
      rfl
    have h1J : (1 : X.ringCatSheaf.obj.obj (op U)) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := h1J
    exact ⟨a, by rw [ha, one_smul]⟩

/-! ## The presheaf tensor product `G A ⊗ G B` localizes on basic opens of an affine open -/

namespace TensorLocAux

variable (A B : X.Modules) {U : X.Opens}

section

variable (f : Γ(X, U))

/-- The restriction ring homomorphism `Γ(U) → Γ(D f)`. -/
abbrev resρ : Γ(X, U) →+* Γ(X, X.basicOpen f) := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom

/-- `Γ(A, D f)` as a `Γ(X, U)`-module via restriction of scalars (used only as a local instance). -/
abbrev locModule : Module Γ(X, U) Γ(A, X.basicOpen f) := Module.compHom _ (resρ (X := X) f)

attribute [local instance] locModule

theorem locModule_smul (r : Γ(X, U)) (x : Γ(A, X.basicOpen f)) :
    r • x = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom r • x := rfl

theorem loc_isScalarTower : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(A, X.basicOpen f) :=
  ⟨fun r s x => by
    rw [locModule_smul, Algebra.smul_def, mul_smul]
    rfl⟩

attribute [local instance] loc_isScalarTower

/-- Restriction `Γ(A, U) → Γ(A, D f)` as a `Γ(X, U)`-linear map. -/
def locRes : Γ(A, U) →ₗ[Γ(X, U)] Γ(A, X.basicOpen f) where
  toFun := A.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' := map_add _
  map_smul' r x := A.map_smul _ r x

theorem locRes_isLocalizedModule [A.IsQuasicoherent] (hU : IsAffineOpen U) :
    IsLocalizedModule (Submonoid.powers f) (locRes A f) :=
  isLocalizedModule_basicOpen A hU f (fun _ _ => rfl) (locRes A f) (fun _ => rfl)

theorem isLoc (hU : IsAffineOpen U) : IsLocalization (Submonoid.powers f) Γ(X, X.basicOpen f) :=
  hU.isLocalization_basicOpen f

/-- The composite `Γ(A, U) ⊗_{Γ(U)} Γ(B, U) → Γ(A, D f) ⊗_{Γ(U)} Γ(B, D f) ≃ Γ(A, D f) ⊗_{Γ(D f)} Γ(B, D f)`
(on pure tensors: restriction in both factors, `locTensor_tmul`). -/
def locTensor (hU : IsAffineOpen U) : Γ(A, U) ⊗[Γ(X, U)] Γ(B, U) →ₗ[Γ(X, U)]
    Γ(A, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(B, X.basicOpen f) :=
  haveI := isLoc f hU
  ((IsLocalization.moduleTensorEquiv (Submonoid.powers f) Γ(X, X.basicOpen f)
    Γ(A, X.basicOpen f) Γ(B, X.basicOpen f)).symm.restrictScalars Γ(X, U)) ∘ₗ
    TensorProduct.map (locRes A f) (locRes B f)

/-- `locTensor` is the localization of `Γ(A, U) ⊗ Γ(B, U)` at the powers of `f` (Mathlib: localization
commutes with `TensorProduct.map`, and `moduleTensorEquiv` changes the base ring). -/
theorem locTensor_isLocalizedModule [A.IsQuasicoherent] [B.IsQuasicoherent] (hU : IsAffineOpen U) :
    IsLocalizedModule (Submonoid.powers f) (locTensor A B f hU) := by
  have := isLoc f hU
  have := locRes_isLocalizedModule A f hU
  have := locRes_isLocalizedModule B f hU
  unfold locTensor
  infer_instance

theorem locTensor_tmul (hU : IsAffineOpen U) (a : Γ(A, U)) (b : Γ(B, U)) :
    locTensor A B f hU (a ⊗ₜ b) =
      A.presheaf.map (homOfLE (X.basicOpen_le f)).op a ⊗ₜ
        B.presheaf.map (homOfLE (X.basicOpen_le f)).op b := by
  have := isLoc f hU
  simp only [locTensor, LinearMap.comp_apply, TensorProduct.map_tmul]
  rfl

/-- The restriction map of the presheaf tensor product `G A ⊗ G B` from `U` to `D(f)`, read in the plain
tensor product `Γ(A, D f) ⊗_{Γ(D f)} Γ(B, D f)`, is `locTensor`. -/
theorem tensorPresheaf_map_eq (hU : IsAffineOpen U)
    (p : ((shG X).obj A ⊗ (shG X).obj B).obj (op U)) :
    ((((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op p :
      Γ(A, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(B, X.basicOpen f))) = locTensor A B f hU p := by
  let g : ((shG X).obj A ⊗ (shG X).obj B).obj (op U) →
      Γ(A, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(B, X.basicOpen f) :=
    fun p => ((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op p
  have hg0 : g 0 = 0 := map_zero (ConcreteCategory.hom
    (((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op))
  have hgadd : ∀ x y, g (x + y) = g x + g y := fun x y => map_add (ConcreteCategory.hom
    (((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op)) x y
  change g p = _
  induction p using TensorProduct.induction_on with
  | zero => exact hg0.trans (map_zero _).symm
  | tmul a b => exact (locTensor_tmul A B f hU a b).symm
  | add x y hx hy => exact (hgadd x y).trans (by rw [hx, hy]; exact (map_add _ x y).symm)

end

attribute [local instance] locModule loc_isScalarTower

/-- (h1) for `P = G A ⊗ G B` on an affine open: a section of `P(U)` dying on `D(f)` is killed by a power of
`f`. (`f` is typed in the ring of the presheaf `X.ringCatSheaf.obj`, which is `Γ(X, U)` up to defeq.) -/
theorem exists_pow_smul_eq_zero [A.IsQuasicoherent] [B.IsQuasicoherent] (hU : IsAffineOpen U)
    (f : X.ringCatSheaf.obj.obj (op U)) (p : ((shG X).obj A ⊗ (shG X).obj B).obj (op U))
    (hp : ((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op p = 0) :
    ∃ n : ℕ, f ^ n • p = 0 := by
  obtain ⟨f, rfl⟩ : ∃ f' : Γ(X, U), (f' : X.ringCatSheaf.obj.obj (op U)) = f := ⟨f, rfl⟩
  have := locTensor_isLocalizedModule A B f hU
  have h0 : locTensor A B f hU p = 0 := by
    rw [← tensorPresheaf_map_eq A B f hU p]; exact hp
  obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) (locTensor A B f hU)).1 h0
  exact ⟨n, hn⟩

/-- (h2) for `P = G A ⊗ G B` on an affine open: a section of `P(D f)` is, after multiplying by a power of
`f`, the restriction of a section of `P(U)`. -/
theorem exists_pow_smul_eq_map [A.IsQuasicoherent] [B.IsQuasicoherent] (hU : IsAffineOpen U)
    (f : X.ringCatSheaf.obj.obj (op U))
    (q : ((shG X).obj A ⊗ (shG X).obj B).obj (op (X.basicOpen f))) :
    ∃ (n : ℕ) (a : ((shG X).obj A ⊗ (shG X).obj B).obj (op U)),
      ((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op a =
        (X.ringCatSheaf.obj.map (homOfLE (X.basicOpen_le f)).op f) ^ n • q := by
  obtain ⟨f, rfl⟩ : ∃ f' : Γ(X, U), (f' : X.ringCatSheaf.obj.obj (op U)) = f := ⟨f, rfl⟩
  have := locTensor_isLocalizedModule A B f hU
  have := isLoc f hU
  obtain ⟨q, rfl⟩ : ∃ q' : Γ(A, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(B, X.basicOpen f),
    (q' : ((shG X).obj A ⊗ (shG X).obj B).obj (op (X.basicOpen f))) = q := ⟨q, rfl⟩
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalizedModule.surj (Submonoid.powers f) (locTensor A B f hU) q
  refine ⟨n, a, ?_⟩
  have ha' : locTensor A B f hU a = (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) • q := by
    rw [algebraMap_smul]; exact ha.symm
  show (((shG X).obj A ⊗ (shG X).obj B).map (homOfLE (X.basicOpen_le f)).op a :
    Γ(A, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(B, X.basicOpen f)) = _
  rw [tensorPresheaf_map_eq A B f hU a, ha', map_pow]
  rfl

end TensorLocAux

/-- **Sections of a tensor product of quasi-coherent modules on an affine open** (Stacks 01I8 for tensor
products). `tensorSectionsHom A B` is the presheaf-level morphism `G A ⊗ G B ⟶ G (A ⊗ B)` (`G` = forget to
presheaves of modules, `ModulesTensorSectionsCoherence.lean`); on `U` it is
`Γ(U, A) ⊗_{Γ(U)} Γ(U, B) → Γ(U, A ⊗ B)`, `a ⊗ b ↦ tensorSections A B U a b` (`tensorSectionsHom_app`).

Proof. `tensorSectionsHom A B = η ≫ G(sheafifyTensorTo A B)` where `η : P → G(L P)` is the sheafification
unit of `P := G A ⊗ G B` (`Adjunction.homEquiv`; pointwise this is the definition of `tensorSections`).
`sheafifyTensorTo A B : L P ≅ A ⊗ B` is an isomorphism, so its value on `U` is bijective, and `L P` is
quasi-coherent (`isQuasicoherent_tensor`). The unit `η` is locally injective and locally surjective (Mathlib,
`toSheafify`). On the affine open `U`, `P` localizes on basic opens (`TensorLocAux.exists_pow_smul_eq_zero`,
`TensorLocAux.exists_pow_smul_eq_map`: `P(D f) = P(U)_f` via Mathlib's localization of tensor products and
`Modules.isLocalizedModule_basicOpen` for `A`, `B`). Hence `η_U` is bijective by
`bijective_app_of_isAffineOpen_of_locallyBijective`, and so is `tensorSectionsHom A B` on `U`.

Edge cases: `U = ⊥` (all modules zero, trivially bijective); `A = 0` or `B = 0` (both sides `0`). -/
theorem tensorSectionsHom_app_bijective_of_isAffineOpen (A B : X.Modules)
    [A.IsQuasicoherent] [B.IsQuasicoherent] {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) :
    Function.Bijective ((AlgebraicGeometry.Scheme.Modules.tensorSectionsHom A B).app (op U)) := by
  let P := (shG X).obj A ⊗ (shG X).obj B
  have : ((shL X).obj P).IsQuasicoherent := isQuasicoherent_tensor A B
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf _).map ((shAdj X).unit.app P)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf _).map ((shAdj X).unit.app P)) :=
    inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf))
  have hunit : Function.Bijective (((shAdj X).unit.app P).app (op U)) :=
    bijective_app_of_isAffineOpen_of_locallyBijective P ((shL X).obj P) ((shAdj X).unit.app P) hU
      (fun f p hp => TensorLocAux.exists_pow_smul_eq_zero A B hU f p hp)
      (fun f q => TensorLocAux.exists_pow_smul_eq_map A B hU f q)
  have : IsIso (sheafifyTensorTo A B) := inferInstanceAs (IsIso (tensorIsoTensorObj A B).hom)
  have : IsIso ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (sheafifyTensorTo A B)) :=
    Functor.map_isIso _ _
  have hs : Function.Bijective ((sheafifyTensorTo A B).val.app (op U)) :=
    ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map (sheafifyTensorTo A B))
  have hθ : ⇑((tensorSectionsHom A B).app (op U)) =
      ⇑((sheafifyTensorTo A B).val.app (op U)) ∘ ⇑(((shAdj X).unit.app P).app (op U)) :=
    funext fun _ => rfl
  rw [hθ]
  exact hs.comp hunit

end AlgebraicGeometry.Scheme.Modules

end
