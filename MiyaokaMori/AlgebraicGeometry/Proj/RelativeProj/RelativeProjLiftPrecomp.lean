import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftLocalPrecomp

/-! # Naturality of the lift into a relative Proj under precomposition

Statement: the construction `relativeProj.lift` of morphisms into a relative Proj is natural under
precomposition. Let `f : T → X`, `M` a line bundle on `T`, `D` a `LiftData` `(Ψ_m : f^*S_m → M^{⊗m})`, and
`g : T' → T`. Then (i) `Ψ'_m := (g^*f^* ≅ (g≫f)^*) ≫ g^*Ψ_m ≫ (g^*(M^{⊗m}) → (g^*M)^{⊗m})` (`precompΨ`) still
preserves the unit and the multiplication and is locally surjective in some positive degree, giving a
`LiftData D.precomp g` for `(S, g ≫ f, g^*M)`; (ii) `lift S (g ≫ f) (g^*M) (D.precomp g) = g ≫ lift S f M D`;
more generally, every `LiftData D'` whose `Ψ`-component equals `precompΨ g D.Ψ` satisfies
`lift D' = g ≫ lift D` (the remaining fields of `LiftData` are propositions).

Proof:
1. Unit (`precompΨ_map_one`): `pullbackComp.inv` is natural in `S.one`, turning `(g≫f)^*(one)` into
   `g^*f^*(one)`; `D.map_one` gives `g^*(pullbackUnitIso f)`; then the compatibility of the unit isomorphism
   with composition, `pullbackComp.inv.app 𝟙 ≫ g^*(pullbackUnitIso f).hom ≫ (pullbackUnitIso g).hom =
   (pullbackUnitIso (g ≫ f)).hom`.
2. Multiplication (`precompΨ_map_mul`): likewise, by naturality of `pullbackComp.inv`, `D.map_mul`, the
   compatibility of `pullbackTensorObjHom` with composition (the lax tensorator of `(g≫f)^*` is the composite of
   those of `g^*` and `f^*`), and the compatibility of `pullbackMonoidalPow g M (m+n)` with `monoidalPowCat`
   (`pullback_map_monoidalPowCat`: induction on `n`, right unit law and associativity of an oplax monoidal
   functor); assembled in the general monoidal lemma `precomp_mul_aux`.
3. Local surjectivity (`precompΨ_generates_at`, pointwise; `precompΨ_generates` follows by applying it at every
   point): for `t' ∈ T'`, take `(U, m)` at `g(t')`; put `U' := g⁻¹U` and `g' := g.resLE U U'`. The first and last
   terms of `(U'.ι)^*precompΨ_m` (`(U'.ι)^*pullbackComp.inv`, `(U'.ι)^*pullbackMonoidalPow`) are isomorphisms —
   `pullbackMonoidalPow` is an isomorphism for **every** module (`isIso_pullbackMonoidalPow_rplp`: degree `0` is
   `pullbackUnitIso`, the induction step `pullbackTensorObjHom_isIso`), no line bundle hypothesis needed; the
   middle term is conjugate via `pullbackComp U'.ι g` to `(U'.ι ≫ g)^*Ψ_m`, `U'.ι ≫ g = g' ≫ U.ι`
   (`resLE_comp_ι`), and then conjugate via `pullbackComp g' U.ι` to `g'^*((U.ι)^*Ψ_m)`; `g'^*` is a left adjoint
   (`pullbackPushforwardAdjunction`) and preserves epimorphisms.
4. Naturality of `lift` (`lift_precomp`; the local leaf is in `RelativeProjLiftLocalPrecomp.lean`):
   `Scheme.hom_ext_of_forall` — for `t' ∈ T'` take a trivialization `(U, e)` of `M` with `g t' ∈ U`, an affine
   `W ∋ f(g t')`, an affine `V ∋ g t'` with `V ≤ U ⊓ f⁻¹W`, and an affine `V' ∋ t'` with `V' ≤ g⁻¹V`. Then
   `V'.ι ≫ lift (D.precomp g) = liftLocal (D.precomp g) (g⁻¹U) (pullbackTrivializationIso g e) W V'`
   (`lift_ι_eq_liftLocal`: the restriction of `lift` to any admissible affine piece is the `liftLocal` of that
   piece, from `liftLocal_compat`) `= g|_{V'→V} ≫ liftLocal D U e W V` (the local leaf
   `liftLocal_precomp_of_Ψ_eq`) `= g|_{V'→V} ≫ V.ι ≫ lift D = V'.ι ≫ g ≫ lift D` (`resLE_comp_ι`).
5. The general form of (ii) (`lift_eq_comp_of_Ψ_eq`): the other three fields of `LiftData` are propositions, so
   equal `Ψ` gives equal structures (`cases` + proof irrelevance); reduce to 4.

Source: Stacks 01O4, 01N8 (morphisms to a relative Proj are compatible with base change). Used for the
projectivization of jets in §2 of the paper (`genericWeightedPoint_eq`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

section MonoidalAux

open MonoidalCategory Functor.OplaxMonoidal

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

/-- Compatibility of the comparison map with the concatenation isomorphism, `n = 0`: the right unitor (right
unit law of an oplax monoidal functor + naturality of `ρ`). -/
private theorem map_rightUnitor_comp (F : C ⥤ D) [F.OplaxMonoidal] {P : C} {Q : D}
    (c : F.obj P ⟶ Q) :
    F.map (ρ_ P).hom ≫ c = δ F P (𝟙_ C) ≫ (c ⊗ₘ η F) ≫ (ρ_ Q).hom := by
  rw [← right_unitality_hom, tensorHom_def']
  simp

/-- Compatibility of the comparison map with the concatenation isomorphism, induction step: the associator
(associativity of an oplax monoidal functor + naturality of `α`). -/
private theorem map_cat_succ_comp (F : C ⥤ D) [F.OplaxMonoidal] {P N V PN : C} {P' N' PN' : D}
    (cP : F.obj P ⟶ P') (cN : F.obj N ⟶ N') (cPN : F.obj PN ⟶ PN')
    (cat : P ⊗ N ⟶ PN) (cat' : P' ⊗ N' ⟶ PN')
    (ih : F.map cat ≫ cPN = δ F P N ≫ (cP ⊗ₘ cN) ≫ cat') :
    F.map ((α_ P N V).inv ≫ cat ▷ V) ≫ δ F PN V ≫ cPN ▷ F.obj V =
      δ F P (N ⊗ V) ≫ (cP ⊗ₘ (δ F N V ≫ cN ▷ F.obj V)) ≫
        (α_ P' N' (F.obj V)).inv ≫ cat' ▷ F.obj V := by
  have h1 : (cP ⊗ₘ (δ F N V ≫ cN ▷ F.obj V)) ≫ (α_ P' N' (F.obj V)).inv =
      F.obj P ◁ δ F N V ≫ (α_ (F.obj P) (F.obj N) (F.obj V)).inv ≫
        (cP ⊗ₘ cN) ▷ F.obj V := by
    rw [← id_tensorHom, ← tensorHom_id, ← tensorHom_id, ← associator_inv_naturality,
      ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [F.map_comp, Category.assoc, ← δ_natural_left_assoc, ← comp_whiskerRight, ih,
    comp_whiskerRight, comp_whiskerRight, ← associativity_inv_assoc, reassoc_of% h1]

/-- Assembly of multiplicativity: if `c : F ⋙ G ≅ H` is compatible with the comultiplication (`hT`), `Ψ` preserves
multiplication (`hmul`), and the comparison map of `G` is compatible with concatenation (`hK`), then the composite
preserves multiplication. -/
private theorem precomp_mul_aux (F : C ⥤ D) (G : D ⥤ E) [G.OplaxMonoidal] (H : C ⥤ E)
    (c : F ⋙ G ≅ H) {A B AB : C} {Ma Mb Mab : D} {Na Nb Nab : E}
    (dF : F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B) (dH : H.obj (A ⊗ B) ⟶ H.obj A ⊗ H.obj B)
    (hT : c.hom.app (A ⊗ B) ≫ dH = G.map dF ≫ δ G (F.obj A) (F.obj B) ≫
      (c.hom.app A ⊗ₘ c.hom.app B))
    (mul : A ⊗ B ⟶ AB) (Ψa : F.obj A ⟶ Ma) (Ψb : F.obj B ⟶ Mb) (Ψab : F.obj AB ⟶ Mab)
    (catM : Ma ⊗ Mb ⟶ Mab) (hmul : F.map mul ≫ Ψab = dF ≫ (Ψa ⊗ₘ Ψb) ≫ catM)
    (pa : G.obj Ma ⟶ Na) (pb : G.obj Mb ⟶ Nb) (pab : G.obj Mab ⟶ Nab) (catN : Na ⊗ Nb ⟶ Nab)
    (hK : G.map catM ≫ pab = δ G Ma Mb ≫ (pa ⊗ₘ pb) ≫ catN) :
    H.map mul ≫ c.inv.app AB ≫ G.map Ψab ≫ pab =
      dH ≫ ((c.inv.app A ≫ G.map Ψa ≫ pa) ⊗ₘ (c.inv.app B ≫ G.map Ψb ≫ pb)) ≫ catN := by
  rw [← cancel_epi (c.hom.app (A ⊗ B)), reassoc_of% hT]
  have hn := c.inv.naturality mul
  rw [reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  rw [← G.map_comp_assoc, hmul,
    G.map_comp_assoc, G.map_comp_assoc, hK, ← δ_natural_assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

end MonoidalAux

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T T' : AlgebraicGeometry.Scheme.{u}} {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules}

/-- The pullback of `Ψ` along `g : T' → T`: `(g ≫ f)^*S_m ≅ g^*f^*S_m → g^*(M^{⊗m}) → (g^*M)^{⊗m}`. -/
def precompΨ (g : T' ⟶ T)
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m) (m : ℕ) :
    (Modules.pullback (g ≫ f)).obj (S.part m) ⟶
      Modules.monoidalPow ((Modules.pullback g).obj M) m :=
  (Modules.pullbackComp g f).inv.app (S.part m) ≫ (Modules.pullback g).map (Ψ m) ≫
    Modules.pullbackMonoidalPow g M m

theorem precompΨ_map_one (g : T' ⟶ T)
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m)
    (h1 : (Modules.pullback f).map S.one ≫ Ψ 0 = (Modules.pullbackUnitIso f).hom) :
    (Modules.pullback (g ≫ f)).map S.one ≫ precompΨ g Ψ 0 =
      (Modules.pullbackUnitIso (g ≫ f)).hom := by
  have hc := Modules.pullbackComp_hom_app_pullbackUnitIso_hom g f
  have hn := (Modules.pullbackComp g f).inv.naturality S.one
  unfold precompΨ
  rw [← Category.assoc, hn]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Modules.pullbackMonoidalPow g M 0)
      (((Modules.pullback g).map_comp _ _).symm.trans (congrArg _ h1))))).trans ?_
  exact (Iso.inv_comp_eq ((Modules.pullbackComp g f).app (𝟙_ X.Modules))).2 hc.symm

/-- The pullback comparison map `pullbackMonoidalPow` is compatible with the concatenation isomorphism
`monoidalPowCat` (induction on `n`: right unit law and associativity). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullback_map_monoidalPowCat (g : T' ⟶ T)
    (M : T.Modules) (m : ℕ) : ∀ n : ℕ,
    (Modules.pullback g).map (Modules.monoidalPowCat M m n).hom ≫
        Modules.pullbackMonoidalPow g M (m + n) =
      Modules.pullbackTensorObjHom g (Modules.monoidalPow M m) (Modules.monoidalPow M n) ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := T'.Modules)
          (Modules.pullbackMonoidalPow g M m) (Modules.pullbackMonoidalPow g M n) ≫
        (Modules.monoidalPowCat ((Modules.pullback g).obj M) m n).hom
  | 0 => by
      -- the `η` of the oplax structure and `pullbackUnitIso.hom` are not `rfl`; use `Modules.pullback_η`
      have h := map_rightUnitor_comp (Modules.pullback g) (Modules.pullbackMonoidalPow g M m)
      rw [Modules.pullback_η] at h
      exact h
  | n + 1 => map_cat_succ_comp (Modules.pullback g) (Modules.pullbackMonoidalPow g M m)
      (Modules.pullbackMonoidalPow g M n) (Modules.pullbackMonoidalPow g M (m + n))
      (Modules.monoidalPowCat M m n).hom (Modules.monoidalPowCat ((Modules.pullback g).obj M) m n).hom
      (Modules.pullback_map_monoidalPowCat g M m n)

theorem precompΨ_map_mul (g : T' ⟶ T)
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m)
    (hmul : ∀ m n : ℕ, (Modules.pullback f).map (S.mul m n) ≫ Ψ (m + n) =
      Modules.pullbackTensorObjHom f (S.part m) (S.part n) ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := T.Modules) (Ψ m) (Ψ n) ≫
        (Modules.monoidalPowCat M m n).hom) (m n : ℕ) :
    (Modules.pullback (g ≫ f)).map (S.mul m n) ≫ precompΨ g Ψ (m + n) =
      Modules.pullbackTensorObjHom (g ≫ f) (S.part m) (S.part n) ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := T'.Modules)
          (precompΨ g Ψ m) (precompΨ g Ψ n) ≫
        (Modules.monoidalPowCat ((Modules.pullback g).obj M) m n).hom :=
  precomp_mul_aux (Modules.pullback f) (Modules.pullback g) (Modules.pullback (g ≫ f))
    (Modules.pullbackComp g f) _ _
    (Modules.pullbackComp_hom_app_pullbackTensorObjHom g f (S.part m) (S.part n))
    (S.mul m n) (Ψ m) (Ψ n) (Ψ (m + n)) (Modules.monoidalPowCat M m n).hom (hmul m n)
    (Modules.pullbackMonoidalPow g M m) (Modules.pullbackMonoidalPow g M n)
    (Modules.pullbackMonoidalPow g M (m + n))
    (Modules.monoidalPowCat ((Modules.pullback g).obj M) m n).hom
    (Modules.pullback_map_monoidalPowCat g M m n)

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback comparison map `pullbackMonoidalPow g M m` is an isomorphism (induction on `m`: degree `0` is
`pullbackUnitIso`, the induction step is `pullbackTensorObjHom` (an isomorphism, `pullbackTensorObjHom_isIso`)
`≫ iso ▷ _`). Same proof as `Modules.isIso_pullbackMonoidalPow` (`RelativeProjLiftMapIrrelevant.lean`), kept
here as a private copy. -/
private theorem isIso_pullbackMonoidalPow_rplp (g : T' ⟶ T) (N : T.Modules) :
    ∀ m : ℕ, IsIso (Modules.pullbackMonoidalPow g N m)
  | 0 => by
    show IsIso (Modules.pullbackUnitIso g).hom
    infer_instance
  | m + 1 => by
    show IsIso (Modules.pullbackTensorObjHom g (Modules.monoidalPow N m) N ≫
      Modules.pullbackMonoidalPow g N m ▷ (Modules.pullback g).obj N)
    have := isIso_pullbackMonoidalPow_rplp g N m
    have := Modules.pullbackTensorObjHom_isIso g (Modules.monoidalPow N m) N
    infer_instance

/-- **Pointwise version**: if `Ψ` is epi in some positive degree near `g(t')`, then `precompΨ` is epi in the same
degree near `t'`.
Take `U' := g⁻¹U` and `g' := g|_{U'} : U' → U` (`Scheme.Hom.resLE`). `(U'.ι)^*(precompΨ_m) =
(U'.ι)^*C⁻¹ ≫ (U'.ι)^*g^*Ψ_m ≫ (U'.ι)^*(pullbackMonoidalPow)`, with first and last terms isomorphisms; the
middle term is conjugate via `pullbackComp U'.ι g` to `(U'.ι ≫ g)^*Ψ_m`, and `U'.ι ≫ g = g' ≫ U.ι`
(`resLE_comp_ι`); `(g' ≫ U.ι)^*Ψ_m` is in turn conjugate to `g'^*((U.ι)^*Ψ_m)` (`pullbackComp g' U.ι`); `g'^*` is
a left adjoint (`pullbackPushforwardAdjunction`) and preserves epimorphisms. -/
theorem precompΨ_generates_at [M.IsLineBundle] (g : T' ⟶ T)
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m) (t' : T')
    (h : ∃ (U : T.Opens) (_ : g.base t' ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((Modules.pullback U.ι).map (Ψ m))) :
    ∃ (U : T'.Opens) (_ : t' ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((Modules.pullback U.ι).map (precompΨ g Ψ m)) := by
  obtain ⟨U, hU, m, hm, hepi⟩ := h
  refine ⟨g ⁻¹ᵁ U, hU, m, hm, ?_⟩
  -- step 1: (g' ≫ U.ι)^*Ψ_m is epi, g' = g.resLE U (g⁻¹U)
  have h1 : Epi ((Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl ≫ U.ι)).map (Ψ m)) := by
    have : (Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        (Modules.pullbackPushforwardAdjunction (g.resLE U (g ⁻¹ᵁ U) le_rfl))
    have h2 : Epi ((Modules.pullback U.ι ⋙ Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).map (Ψ m)) :=
      Functor.map_epi (Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)) ((Modules.pullback U.ι).map (Ψ m))
    rw [← NatIso.naturality_1 (Modules.pullbackComp (g.resLE U (g ⁻¹ᵁ U) le_rfl) U.ι) (Ψ m)]
    infer_instance
  -- step 2: g' ≫ U.ι = (g⁻¹U).ι ≫ g
  rw [Scheme.Hom.resLE_comp_ι] at h1
  -- step 3: transport back to (g⁻¹U).ι^* g^* Ψ_m
  have h3 : Epi ((Modules.pullback g ⋙ Modules.pullback (g ⁻¹ᵁ U).ι).map (Ψ m)) := by
    rw [← NatIso.naturality_2 (Modules.pullbackComp (g ⁻¹ᵁ U).ι g) (Ψ m)]
    infer_instance
  -- step 4: the first and last terms of precompΨ are isomorphisms
  have h4 : Epi ((Modules.pullback (g ⁻¹ᵁ U).ι).map ((Modules.pullback g).map (Ψ m))) := h3
  have h5 := isIso_pullbackMonoidalPow_rplp g M m
  unfold precompΨ
  rw [Functor.map_comp, Functor.map_comp]
  infer_instance

theorem precompΨ_generates [M.IsLineBundle] (g : T' ⟶ T)
    (Ψ : ∀ m : ℕ, (Modules.pullback f).obj (S.part m) ⟶ Modules.monoidalPow M m)
    (hgen : ∀ t : T, ∃ (U : T.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((Modules.pullback U.ι).map (Ψ m))) :
    ∀ t : T', ∃ (U : T'.Opens) (_ : t ∈ U) (m : ℕ) (_ : 0 < m),
      CategoryTheory.Epi ((Modules.pullback U.ι).map (precompΨ g Ψ m)) :=
  fun t => precompΨ_generates_at g Ψ t (hgen (g.base t))

/-- The pullback of a `LiftData` along `g : T' → T`. -/
def LiftData.precomp [M.IsLineBundle] (D : LiftData S f M) (g : T' ⟶ T) :
    LiftData S (g ≫ f) ((Modules.pullback g).obj M) where
  Ψ := precompΨ g D.Ψ
  map_one := precompΨ_map_one g D.Ψ D.map_one
  map_mul := precompΨ_map_mul g D.Ψ D.map_mul
  generates := precompΨ_generates g D.Ψ D.generates

/-- **`lift` is natural under precomposition**: `lift (D.precomp g) = g ≫ lift D`.
Proof: both sides are morphisms `T' → Proj_X S`; by `Scheme.hom_ext_of_forall` it suffices to find,
around each `t' : T'`, an open `V'` on which they agree. Take a trivialization `e` of `M` on `U ∋ g t'`, an affine
`W ∋ f (g t')`, an affine `V ∋ g t'` with `V ≤ U ⊓ f⁻¹W`, and an affine `V' ∋ t'` with `V' ≤ g⁻¹V`. Then
`V'.ι ≫ lift (D.precomp g) = liftLocal (D.precomp g) (g⁻¹U) (g^*e) W V'` (`lift_ι_eq_liftLocal`),
`= g|_{V'→V} ≫ liftLocal D U e W V` (`liftLocal_precomp_of_Ψ_eq`, the local leaf, `RelativeProjLiftLocalPrecomp.lean`),
`= g|_{V'→V} ≫ V.ι ≫ lift D` (`lift_ι_eq_liftLocal` again) `= V'.ι ≫ g ≫ lift D` (`resLE_comp_ι`). -/
theorem lift_precomp [M.IsLineBundle] (D : LiftData S f M) (g : T' ⟶ T) :
    lift S (g ≫ f) ((Modules.pullback g).obj M) (D.precomp g) = g ≫ lift S f M D := by
  refine Scheme.hom_ext_of_forall _ _ fun t' => ?_
  obtain ⟨U, hU, ⟨e⟩⟩ := Modules.IsLineBundle.locally_trivial (M := M) (g.base t')
  obtain ⟨W, hW, hfW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := f.base (g.base t')) (U := ⊤) trivial
  obtain ⟨V, hV, htV, hVle⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := g.base t') (U := U ⊓ f ⁻¹ᵁ W) ⟨hU, hfW⟩
  obtain ⟨V', hV', htV', hV'le⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := t') (U := g ⁻¹ᵁ V) htV
  have hle : V ≤ U ⊓ f ⁻¹ᵁ W := hVle
  have h : V' ≤ g ⁻¹ᵁ V := hV'le
  refine ⟨V', htV', ?_⟩
  rw [lift_ι_eq_liftLocal S (g ≫ f) _ (D.precomp g) (g ⁻¹ᵁ U) (Modules.pullbackTrivializationIso g e)
      ⟨W, hW⟩ V' hV' (precomp_le g hle h),
    ← liftLocal_precomp_of_Ψ_eq S f M D g (D.precomp g) (fun _ => rfl) U e ⟨W, hW⟩ V hV hle V' hV' h,
    ← Category.assoc, ← Scheme.Hom.resLE_comp_ι g h, Category.assoc,
    lift_ι_eq_liftLocal S f M D U e ⟨W, hW⟩ V hV hle]

/-- Any `LiftData` whose `Ψ`-component equals `precompΨ` gives the same morphism (the remaining fields are
propositions). -/
theorem lift_eq_comp_of_Ψ_eq [M.IsLineBundle] (D : LiftData S f M) (g : T' ⟶ T)
    (D' : LiftData S (g ≫ f) ((Modules.pullback g).obj M)) (hΨ : D'.Ψ = precompΨ g D.Ψ) :
    lift S (g ≫ f) ((Modules.pullback g).obj M) D' = g ≫ lift S f M D := by
  have : D' = D.precomp g := by
    cases D'
    simp only [LiftData.precomp]
    congr
  rw [this, lift_precomp]

end AlgebraicGeometry.Scheme.relativeProj

end
