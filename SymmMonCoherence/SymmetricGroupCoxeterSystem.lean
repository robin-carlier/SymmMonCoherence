module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.List.Intervals
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Infix
public import Mathlib.Algebra.PresentedMonoid.Basic
public import Init.Data.List.Sublist
public import SymmMonCoherence.CoxeterGroupRecognition

@[expose] public section

def FreeMonoid.toFreeGroup (X : Type*) : FreeMonoid X →* FreeGroup X :=
  FreeMonoid.lift (fun x ↦ .of x)

@[simp]
lemma FreeMonoid.toFreeGroup_of (X : Type*) (x : X) : FreeMonoid.toFreeGroup X (.of x) = .of x :=
  rfl

@[simp]
lemma PresentedMonoid.mk_of {X : Type*} (r : FreeMonoid X → FreeMonoid X → Prop) (x : X) :
    PresentedMonoid.mk r (.of x) = .of r x :=
  rfl

variable (n : ℕ)

attribute [local grind =] Equiv.Perm.mul_apply Equiv.Perm.one_apply

private lemma Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne {α : Type*} [DecidableEq α]
      (a b c d : α) (_ : a ≠ b) (_ : a ≠ c) (_ : c ≠ d)
      (hb : (c = b ∧ d ≠ a) ∨ (d = a ∧ c ≠ b)) :
    orderOf ((Equiv.swap a b) * (Equiv.swap c d)) = 3 := by
  rw [orderOf_eq_prime (p := 3)]
  · grind (splits := 16) [swap_apply_of_ne_of_ne, pow_three]
  · intro h
    have e₄ := congr($h d)
    grind [swap_apply_of_ne_of_ne]

private lemma Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup
    {α : Type*} [DecidableEq α] (a b c d : α) (h : [a, b, c, d].Nodup) :
    orderOf ((Equiv.swap a b) * (Equiv.swap c d)) = 2 := by
  rw [orderOf_eq_prime (p := 2)]
  · grind (splits := 16) [swap_apply_of_ne_of_ne, pow_two]
  · intro h
    have := congr($h a)
    grind

attribute [local ext, local grind ext] Fin.ext in
attribute [local grind =] Fin.val_castSucc in
/-- The canonical morphism that realizes the Coxeter group of the Coxeter matrix Aₙ
in the symmetric group. It sends the generator `i` to the transposition `(i, i + 1)`. -/
def CoxeterMatrix.Aₙ_to_perm : (CoxeterMatrix.Aₙ n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift
    ⟨fun i ↦ Equiv.swap i.castSucc i.succ, fun i j => by
        have succ_ne_castSucc : ∀ (i : Fin n), i.succ ≠ i.castSucc := by grind
        dsimp [CoxeterMatrix.Aₙ]
        split_ifs with h h' <;> (convert pow_orderOf_eq_one _; symm)
        · subst h
          simp
        · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne]
        · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup]⟩

@[simp]
lemma CoxeterMatrix.Aₙ_to_perm_simple {n : ℕ} (j : Fin n) :
    CoxeterMatrix.Aₙ_to_perm n ((CoxeterMatrix.Aₙ n).simple j) = Equiv.swap j.castSucc j.succ := rfl

@[simp]
lemma CoxeterMatrix.Aₙ_to_perm_simple' {n : ℕ} (j : Fin n) :
    CoxeterMatrix.Aₙ_to_perm n ((CoxeterMatrix.Aₙ n).toCoxeterSystem.simple j) =
    Equiv.swap j.castSucc j.succ := rfl

attribute [local ext, local grind ext] Fin.ext in
attribute [local grind =] Fin.val_succ Fin.coe_castSucc in
def Fin.preCoxeterSystem :
    PreCoxeterSystem (CoxeterMatrix.Aₙ n) (Equiv.Perm (Fin (n + 1))) where
  hom := CoxeterMatrix.Aₙ_to_perm n
  surjective_hom := by
    -- Equiv.Perm.mclosure_swap_castSucc_succ
    rw [← MonoidHom.mrange_eq_top, eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ n]
    -- have := Equiv.Perm.mclosure_swap_castSucc_succ n
    simp only [Submonoid.closure_le, MonoidHom.coe_mrange, Set.range_subset_iff, Set.mem_range]
    intro i
    exact ⟨(CoxeterMatrix.Aₙ n).toCoxeterSystem.simple i, rfl⟩
  orderOf_eq i j := by
    -- TODO prove this separately and use in the def of Aₙ_to_perm instead
    have succ_ne_castSucc : ∀ (i : Fin n), i.succ ≠ i.castSucc := by
      grind
    simp only [CoxeterMatrix.Aₙ_to_perm_simple]
    simp only [CoxeterMatrix.Aₙ, Matrix.of_apply]
    split_ifs with h h' <;> symm
    · subst h
      simp
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne]
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup]
  hom_simple_ne_one i := by
    simp only [CoxeterMatrix.Aₙ_to_perm_simple, ne_eq, Equiv.swap_eq_one_iff]
    grind

@[simp, grind =]
lemma preCoxeterSystem_hom_simple (i : Fin n) :
    (Fin.preCoxeterSystem n).hom ((CoxeterMatrix.Aₙ n).simple i) =
    Equiv.swap i.castSucc i.succ :=
  rfl

section exchange

variable {n}

abbrev Fin.inversionSet (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
   { i | i.1 < i.2 ∧ σ i.1 > σ i.2 }

local prefix:100 "ℐ " => Fin.inversionSet

def Fin.inversionNumber (σ : Equiv.Perm (Fin n)) : ℕ :=
  Finset.card <| ℐ σ

local prefix:100 "ι " => Fin.inversionNumber

local notation "Ψ " x:max => Equiv.swap (Fin.castSucc x) (Fin.succ x)

private lemma inversionSet_mul_swap_castSucc_succ_eq_of_le
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) (hi : σ i.castSucc < σ i.succ) :
    ℐ (σ * Ψ i) = Finset.image (Equiv.prodCongr (Ψ i) (Ψ i)) (ℐ σ) ∪ {(i.castSucc, i.succ)} := by
  let τ : Equiv.Perm (Fin (n + 1) × Fin (n + 1)) :=
    Equiv.prodCongr (Ψ i) (Ψ i)
  have not_mem : ⟨i.castSucc, i.succ⟩ ∉ Fin.inversionSet σ := by grind
  -- Then, it is an inversion in the next:
  have mem : ⟨i.castSucc, i.succ⟩ ∈
      Fin.inversionSet (σ * (Equiv.swap i.succ i.castSucc)) := by simpa
  have : Finset.image τ (ℐ σ) ⊆
      Fin.inversionSet (σ * Ψ i) := by
    simp only [Equiv.prodCongr_apply, Finset.subset_iff, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, gt_iff_lt, true_and, Prod.exists, Prod.map_apply, Equiv.Perm.coe_mul,
      Function.comp_apply, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq, τ]
    intro a b a' b' hab hsab _ _
    grind [Fin.lt_def]
  have (i₀ j₀ : Fin (n + 1)) (hij₀ : (i₀, j₀) ∈ ℐ (σ * Ψ i)) :
      ((i₀, j₀) ∈ Finset.image τ (ℐ σ) ∨ (i₀, j₀) = (i.castSucc, i.succ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, Equiv.Perm.coe_mul, Function.comp_apply,
      gt_iff_lt, true_and] at hij₀
    obtain ⟨hij₀, hσij₀⟩ := hij₀
    simp only [Equiv.prodCongr_apply, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      gt_iff_lt, true_and, Prod.exists, Prod.map_apply, Prod.mk.injEq, τ]
    by_cases h : i₀ = i.castSucc
    · subst h
      grind [Fin.lt_def]
    · by_cases h : j₀ = i.succ
      · subst h
        left
        use i₀, i.castSucc
        grind [Fin.lt_def]
      · left
        by_cases h : j₀ = i.castSucc
        · have : i₀ ≠ i.succ := by grind [Fin.lt_def]
          subst h
          rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)] at hσij₀
          use i₀, i.succ
          grind
        · grind [Fin.lt_def, Equiv.swap_apply_of_ne_of_ne]
  grind

lemma inversionNumber_mul_swap_castSucc_succ_eq_of_le (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (h : σ i.castSucc < σ i.succ) :
    ι (σ * (Ψ i)) = (ι σ) + 1 := by
  have not_mem : ⟨i.castSucc, i.succ⟩ ∉ Fin.inversionSet σ := by
    grind
  -- Then, it is an inversion in the next:
  have mem : ⟨i.castSucc, i.succ⟩ ∈
      Fin.inversionSet (σ * (Equiv.swap i.succ i.castSucc)) := by
    simpa
  have := congr(Finset.card $(inversionSet_mul_swap_castSucc_succ_eq_of_le σ i h))
  rw [Finset.card_union_of_disjoint] at this
  · simp only [Equiv.prodCongr_apply, Finset.card_singleton] at this
    rwa [Finset.card_image_iff.mpr _] at this
    simp
  · simp only [Equiv.prodCongr_apply, Finset.disjoint_singleton_right, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, gt_iff_lt, true_and, Prod.exists, Prod.map_apply,
      Prod.mk.injEq, not_exists, not_and, and_imp]
    grind

lemma inversionNumber_mul_swap_castSucc_succ_eq_of_le' (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (h : σ i.succ < σ i.castSucc) :
    ι (σ * (Ψ i)) = (ι σ) - 1 := by
  let φ := σ * (Ψ i)
  have := inversionNumber_mul_swap_castSucc_succ_eq_of_le φ i (by grind)
  grind [Equiv.mul_swap_mul_self]

lemma inversionNumber_mul_swap_castSucc_succ_eq (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    ι (σ * (Ψ i)) = if (σ i.castSucc < σ i.succ) then (ι σ) + 1 else (ι σ) - 1 := by
  grind [Equiv.injective, Fin.lt_def,
    inversionNumber_mul_swap_castSucc_succ_eq_of_le,
    inversionNumber_mul_swap_castSucc_succ_eq_of_le']

theorem inversionNumber_one : ι (1 : Equiv.Perm (Fin n)) = 0 := by
  dsimp [Fin.inversionNumber, Fin.inversionSet]
  grind [gt_iff_lt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_lt]

lemma inversionSet_swap_castSucc (i : Fin n) : ℐ (Ψ i) = {(i.castSucc, i.succ)} := by
  ext ⟨i₀, j₀⟩
  grind [Fin.lt_def]

lemma inversionNumber_swap_castSucc_succ (i : Fin n) :
    ι (Ψ i) = 1 := by
  dsimp [Fin.inversionNumber]
  rw [inversionSet_swap_castSucc, Finset.card_singleton]

theorem inversionNumber_le_length (σ : Equiv.Perm (Fin (n + 1))) :
    ι σ ≤ (Fin.preCoxeterSystem n).length σ := by
  obtain ⟨ω, hω, hred⟩ := Fin.preCoxeterSystem n |>.exists_reduced_word σ
  rw [← hω, ← hred]
  clear hω hred
  induction ω using List.reverseRecOn generalizing σ with
  | nil => simpa using inversionNumber_one
  | append_singleton ω s ih =>
    simp only [Fin.preCoxeterSystem, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_singleton, CoxeterMatrix.toCoxeterSystem_simple, map_mul,
      CoxeterMatrix.Aₙ_to_perm_simple, List.length_append, List.length_cons, List.length_nil,
      zero_add] at ⊢
    simp only [forall_const] at ih
    rw [inversionNumber_mul_swap_castSucc_succ_eq]
    suffices h :
        ι (CoxeterMatrix.Aₙ_to_perm n) ((CoxeterMatrix.Aₙ n).toCoxeterSystem.wordProd ω) ≤
          ω.length by grind
    exact ih

lemma inversionNumber_eq_zero_iff (σ : Equiv.Perm (Fin n)) :
    ι σ = 0 ↔ σ = 1 where
  mp h := by
    simp only [Fin.inversionNumber, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, gt_iff_lt, not_and, not_lt, forall_const, Prod.forall] at h
    have : StrictMono σ := by
      intro a b h
      grind [Equiv.injective]
    have : σ = @id (Fin n) := le_antisymm (StrictMono.le_id this) (StrictMono.id_le this)
    ext x
    exact congr($this x)
  mpr h := by grind [inversionNumber_one]

theorem length_le_inversionNumber (σ : Equiv.Perm (Fin (n + 1))) :
   (Fin.preCoxeterSystem n).length σ ≤ ι σ := by
  induction h : ι σ generalizing σ with
  | zero => simpa [← inversionNumber_eq_zero_iff] using h
  | succ k ih =>
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ι (σ * (Ψ i)) = k := by
      by_contra! h'
      simp only [inversionNumber_mul_swap_castSucc_succ_eq, h, add_tsub_cancel_right, ne_eq,
        ite_eq_right_iff, Classical.not_imp] at h'
      suffices σ = 1 by grind [inversionNumber_one]
      suffices StrictMono σ by
        have := le_antisymm (StrictMono.le_id this) (StrictMono.id_le this)
        ext x
        exact congr($this x)
      exact Fin.strictMono_iff_lt_succ.mpr (by grind)
    have hr := ih (σ * (Ψ i)) hi
    have le' := (Fin.preCoxeterSystem n).length_mul_le (σ * (Ψ i)) (Ψ i)
    have : (Fin.preCoxeterSystem n).length (Ψ i) = 1 := by
      simpa using (Fin.preCoxeterSystem n).length_simple i
    simp only [Equiv.mul_swap_mul_self, this] at le'
    grind

theorem length_eq_inversionNumber (σ : Equiv.Perm (Fin (n + 1))) :
   (Fin.preCoxeterSystem n).length σ = ι σ :=
  le_antisymm (length_le_inversionNumber σ) (inversionNumber_le_length σ)

-- Local non-hygienic notation, but really saves space.
set_option quotPrecheck false in
local notation "φ " x:max =>
    (Fin.preCoxeterSystem n).hom ((CoxeterMatrix.Aₙ n).toCoxeterSystem.wordProd x)

-- _root_.List.getElem_inits_eq_take

theorem exchange : (Fin.preCoxeterSystem n).ExchangeProperty' := by
  intro ω hω i hi
  simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
    CoxeterMatrix.toCoxeterSystem_simple, map_mul, preCoxeterSystem_hom_simple, exists_prop] at hi ⊢
  dsimp [PreCoxeterSystem.IsReduced] at hω
  rw [← hω]
  set σ := φ ω
  simp only [length_eq_inversionNumber] at *
  have inversion : σ i.succ < σ i.castSucc := by
    grind [inversionNumber_mul_swap_castSucc_succ_eq, Equiv.injective,
      Fin.lt_def]
  -- Names and notations from Björner-Brenti
  let b := σ i.castSucc
  let a := σ i.succ
  have a_ne_b : a ≠ b := by grind
  -- if ω = [s₁, …, sₖ], consider the first index for which [s₁,…, sᵢ] "inverts b and a"
  let i₀ := ω.inits.findIdx (fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a)
  -- as [s₁,…, sₖ] inverts a and b, i₀ is at least < ω.length + 1,
  -- (the number of initial sublists of ω)
  have hi₀ : i₀ < ω.length + 1 := by
    dsimp [i₀]
    rw [← List.length_inits, List.findIdx_lt_length]
    exact ⟨ω, by simp, by simp [a, b, σ]⟩
  -- as [] does not invert a and b, 0 < i₀
  have hi₀' : 0 < i₀ := by
    dsimp [i₀]
    apply List.lt_findIdx_of_not
    · intro j hj
      simp only [nonpos_iff_eq_zero] at hj
      subst hj
      simpa [a, b, σ] using inversion.le
    · simp
  -- by definition, ω.take i₀ "inverts b and a"
  have inv₀ : (φ (ω.take i₀))⁻¹ b < (φ (ω.take i₀))⁻¹ a := by
    simpa using
      ω.inits.findIdx_getElem (p := fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a) (w := by simpa using hi₀)
  have inv₁ : ∀ j < i₀, (φ (ω.take j))⁻¹ a < (φ (ω.take j))⁻¹ b := by
    intro j hj
    have : (φ (ω.take j))⁻¹ a ≤ (φ (ω.take j))⁻¹ b := by
      simpa using ω.inits.not_of_lt_findIdx (p := fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a) hj
    grind [Equiv.injective]
  obtain ⟨i'', hi''⟩ := Nat.exists_add_one_eq.mpr hi₀'
  simp only [← hi'', Equiv.Perm.coe_inv, add_lt_add_iff_right, lt_add_iff_pos_left, add_pos_iff,
    zero_lt_one, or_true] at inv₀ inv₁ hi₀ hi₀'
  rw [List.take_succ_eq_append_getElem hi₀] at inv₀
  -- Let’s use this index.
  use i''
  refine ⟨by grind, ?_⟩
  ext k : 1
  -- We compute ω[i''] in terms of i
  obtain ⟨e₁, e₂⟩ :
    (φ (ω.drop i'')) i.succ = ω[i''].castSucc ∧
      (φ (ω.drop i'')) i.castSucc = ω[i''].succ := by
    -- The idea is to show this is an inversion for Equiv.swap ω[i''].castSucc ω[i''].succ.
    have inv₀' := inv₁ i'' (lt_add_one i'')
    simp only [↓CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
      CoxeterMatrix.toCoxeterSystem_simple, map_mul, preCoxeterSystem_hom_simple,
      ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
      Function.comp_apply, a, σ, b] at inv₀ inv₀'
    nth_rewrite 4 8 [← ω.take_append_drop i''] at inv₀
    nth_rewrite 2 4 [← ω.take_append_drop i''] at inv₀'
    simp only [↓CoxeterSystem.wordProd_append, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.symm_apply_apply] at inv₀ inv₀'
    have : ((φ (ω.drop i'')) i.succ, (φ (ω.drop i'')) i.castSucc) ∈ (ℐ (Ψ ω[i''])) := by
      grind
    simpa [inversionSet_swap_castSucc] using this
  obtain ⟨e₁', e₂'⟩ :
    (φ (ω.drop (i'' + 1))) i.succ = ω[i''].succ ∧
      (φ (ω.drop (i'' + 1))) i.castSucc = ω[i''].castSucc := by
    nth_rewrite 1 [← (ω.drop i'').cons_head_tail (by simpa using hi₀)] at e₁ e₂
    simp only [↓CoxeterSystem.wordProd_cons, List.head_drop, CoxeterMatrix.toCoxeterSystem_simple,
      List.tail_drop, map_mul, preCoxeterSystem_hom_simple, Equiv.Perm.coe_mul,
      Function.comp_apply] at e₁ e₂
    grind
  -- Thanks to that computation, we can now compute the value on both sides depending on
  -- whether or not `k ∈ {i.castSucc, i.succ}`, and observe the results are the same.
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, List.eraseIdx_eq_take_drop_succ,
    CoxeterSystem.wordProd_append, map_mul]
  by_cases! hk : k = i.castSucc ∨ k = i.succ
  · dsimp [σ, a, b]
    nth_rewrite 1 [← ω.take_append_drop i'']
    simp only [↓CoxeterSystem.wordProd_append, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq]
    grind
  · rw [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2]
    dsimp [σ]
    nth_rewrite 1 [← ω.take_append_drop (i'' + 1), List.take_succ_eq_append_getElem hi₀]
    simp only [↓CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
      CoxeterMatrix.toCoxeterSystem_simple, map_mul, preCoxeterSystem_hom_simple,
      Equiv.Perm.coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
    grind [Equiv.swap_apply_of_ne_of_ne, Equiv.injective]

end exchange

theorem injective_Aₙ_to_perm (n : ℕ) : Function.Injective (CoxeterMatrix.Aₙ_to_perm n) :=
  (Fin.preCoxeterSystem n).injective_hom_of_exchangeProperty <|
   (Fin.preCoxeterSystem n).exchangeProperty_iff_exchangeProperty'.mpr exchange

theorem bijective_hom1 (n : ℕ) : Function.Bijective (CoxeterMatrix.Aₙ_to_perm n) :=
  ⟨injective_Aₙ_to_perm n, (Fin.preCoxeterSystem n).surjective_hom⟩

noncomputable def hom1MulEquiv (n : ℕ) : (CoxeterMatrix.Aₙ n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective _ (bijective_hom1 n)

attribute [-simp] CoxeterMatrix.toCoxeterSystem_simple

@[simps]
def Ainf : CoxeterMatrix ℕ where
  M := Matrix.of fun i j : ℕ ↦
    if i = j then 1
      else (if j + 1 = i ∨ i + 1 = j then 3 else 2)
  isSymm := by unfold Matrix.IsSymm; aesop
  diagonal := by simp
  off_diagonal := by aesop

lemma Aₙ_m_eq (i j : Fin n) : (CoxeterMatrix.Aₙ n).M i j = Ainf.M ↑i ↑j := by
  dsimp [CoxeterMatrix.Aₙ]
  grind

def AnToAinf (n : ℕ) : (CoxeterMatrix.Aₙ n).Group →* Ainf.Group :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift
    ⟨fun k ↦ Ainf.toCoxeterSystem.simple k.val, by
      intro i i'
      rw [Aₙ_m_eq, CoxeterSystem.simple_mul_simple_pow]⟩

@[simp, grind =]
lemma AnToAinf_simple (n : ℕ) (i : Fin n) :
    (AnToAinf n) ((CoxeterMatrix.Aₙ n).toCoxeterSystem.simple i) = Ainf.toCoxeterSystem.simple i :=
  rfl

def AinfToPerm : Ainf.Group →* Equiv.Perm ℕ :=
  Ainf.toCoxeterSystem.lift ⟨fun k ↦ Equiv.swap k (k + 1), fun i j => by
    dsimp [CoxeterMatrix.Aₙ]
    split_ifs with h h' <;> (convert pow_orderOf_eq_one _; symm)
    · subst h
      simp
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne]
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup]⟩

theorem Ainf.exists_lift_to_Aₙ (x : Ainf.Group) :
    ∃ (n : ℕ) (x' : (CoxeterMatrix.Aₙ n).Group), x = AnToAinf n x' := by
  obtain ⟨ω, -, rfl⟩ := Ainf.toCoxeterSystem.exists_reduced_word x
  obtain ⟨m, inst, hm⟩ : ∃ (m : ℕ) (hm : NeZero m), ∀ i ∈ ω, i < m := by
    by_cases! h : ω = []
    · use 1, by infer_instance
      grind
    · use ω.max h + 1, by infer_instance
      intro i hi
      simpa [← Nat.le_iff_lt_add_one] using List.le_max_of_mem hi
  use m, CoxeterMatrix.Aₙ m |>.toCoxeterSystem.wordProd (ω.map (Fin.ofNat m))
  induction ω generalizing m with
  | nil => simp
  | cons s ω ih =>
    have : s % m = s := by
      apply Nat.mod_eq_of_lt
      exact hm s (by tauto)
    simp only [CoxeterSystem.wordProd_cons, List.map_cons, Fin.ofNat_eq_cast, map_mul,
      AnToAinf_simple, Fin.val_natCast, this, mul_right_inj]
    apply ih
    intro i hi
    exact hm i (by tauto)

@[simp]
lemma AinfToPerm_simple (i : ℕ) :
    AinfToPerm (Ainf.toCoxeterSystem.simple i) = Equiv.swap i (i + 1) :=
  rfl

@[simp]
lemma AinfToPerm_simple' (i : ℕ) :
    AinfToPerm (Ainf.simple i) = Equiv.swap i (i + 1) :=
  rfl

/-- Lifting `Fin.castLE` to a morphism from `(Aₙ n).Group` to `(Aₙ m).Group` -/
def Aₙ.castLE {n m : ℕ} (h : n ≤ m) : (CoxeterMatrix.Aₙ n).Group →* (CoxeterMatrix.Aₙ m).Group :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift
    ⟨fun k ↦ (CoxeterMatrix.Aₙ m).toCoxeterSystem.simple (k.castLE h), by
      intro i i'
      dsimp
      have h (i j : Fin n) :
          (CoxeterMatrix.Aₙ n).M i j = (CoxeterMatrix.Aₙ m).M (i.castLE h) (j.castLE h) := by
        simp [CoxeterMatrix.Aₙ]
      simp [h] ⟩

@[simp, grind =]
lemma Aₙ.castLE_simple {n m : ℕ} {h : n ≤ m} (i : Fin n) :
    Aₙ.castLE h ((CoxeterMatrix.Aₙ n).simple i) = (CoxeterMatrix.Aₙ m).simple (i.castLE h) := rfl

@[simp, grind =]
lemma Aₙ.castLE_simple' {n m : ℕ} {h : n ≤ m} (i : Fin n) :
    Aₙ.castLE h ((CoxeterMatrix.Aₙ n).toCoxeterSystem.simple i) =
      (CoxeterMatrix.Aₙ m).toCoxeterSystem.simple (i.castLE h) := rfl

@[simp]
lemma Aₙ.castLE_toAinf {n m : ℕ} {h : n ≤ m} :
    (AnToAinf _).comp (Aₙ.castLE h) = AnToAinf _ := by
  apply (CoxeterMatrix.Aₙ n).toCoxeterSystem.ext_simple
  intro i
  rfl

lemma Aₙ_to_perm_extend (n : ℕ) :
    (Equiv.Perm.extendDomainHom Fin.equivSubtype).comp (CoxeterMatrix.Aₙ_to_perm n) =
    AinfToPerm.comp (AnToAinf n) := by
  apply (CoxeterMatrix.Aₙ n).toCoxeterSystem.ext_simple
  intro i
  simp only [MonoidHom.coe_comp, Function.comp_apply, CoxeterMatrix.Aₙ_to_perm_simple',
    Equiv.Perm.extendDomainHom_apply, AinfToPerm, AnToAinf, CoxeterSystem.lift_apply_simple]
  ext j
  by_cases h : j < n + 1
  · rw [Equiv.Perm.extendDomain_apply_subtype (b := j) (h := h)]
    simp [Fin.equivSubtype_symm_apply, Equiv.swap_apply_def, Fin.equivSubtype_apply,
      apply_ite (f := Fin.val), Fin.ext_iff]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ Fin.equivSubtype h,
      Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)]

lemma Aₙ_to_perm_apply_eq (n : ℕ) (i : Fin (n + 1))
    (w : (CoxeterMatrix.Aₙ n).Group) :
    CoxeterMatrix.Aₙ_to_perm n w i = AinfToPerm (AnToAinf n w) i := by
  have := congr($(Aₙ_to_perm_extend n) w i)
  simp only [MonoidHom.coe_comp, Function.comp_apply, Equiv.Perm.extendDomainHom_apply] at this
  rw [Equiv.Perm.extendDomain_apply_subtype] at this
  · exact this
  · grind

abbrev shift' : (FreeGroup ℕ) →* (FreeGroup ℕ) := FreeGroup.lift (.of <| · + 1)

abbrev shift'Mon (k : ℕ) : (FreeMonoid ℕ) →* (FreeMonoid ℕ) := FreeMonoid.lift (.of <| · + k)

lemma shift'Mon_self (k l : ℕ) (w : FreeMonoid ℕ) :
    shift'Mon k (shift'Mon l w) = shift'Mon (l + k) w := by
  induction w with grind [FreeMonoid.lift_eval_of]

@[simp, grind =]
lemma shift'Mon_zero (w : FreeMonoid ℕ) :
    shift'Mon 0 w = w := by
  induction w with grind [FreeMonoid.lift_eval_of]

abbrev succMon : (FreeMonoid (Fin n)) →* FreeMonoid (Fin <| n + 1) :=
  FreeMonoid.lift (.of <| Fin.succ ·)

def Ainf.shift (k : ℕ) : Ainf.Group →* Ainf.Group :=
  Ainf.toCoxeterSystem.lift ⟨fun n ↦ Ainf.toCoxeterSystem.simple (n + k), by
    intro i i'
    simp only [Ainf_M, Matrix.of_apply, pow_ite, pow_one]
    split_ifs with h h'
    · simp [h]
    · obtain rfl | rfl := h'
      · rw [add_right_comm i' 1 k]
        have : Ainf.M (i' + k + 1) (i' + k) = 3 := by simp [Ainf_M, Matrix.of_apply, add_assoc]
        rw [← this]
        exact Ainf.toCoxeterSystem.simple_mul_simple_pow (i' + k + 1) (i' + k)
      · rw [add_right_comm i 1 k]
        have : Ainf.M (i + k) (i + k + 1) = 3 := by simp [Ainf_M, Matrix.of_apply, add_assoc]
        rw [← this]
        exact Ainf.toCoxeterSystem.simple_mul_simple_pow (i + k) (i + k + 1)
    · have := Ainf.toCoxeterSystem.simple_mul_simple_pow (i + k) (i' + k)
      simp only [Ainf_M, Matrix.of_apply, Nat.add_right_cancel_iff, pow_ite, pow_one] at this
      grind ⟩

@[simp]
lemma Ainf.shift_simple (k n : ℕ) : Ainf.shift k (Ainf.simple n) = Ainf.simple (n + k) := rfl

@[simp]
lemma Ainf.shift_simple' (k n : ℕ) :
    Ainf.shift k (Ainf.toCoxeterSystem.simple n) = Ainf.toCoxeterSystem.simple (n + k) := rfl

lemma Ainf.shift_shift (k k' : ℕ) (x : Ainf.Group) :
    Ainf.shift k (Ainf.shift k' x) = Ainf.shift (k + k') x := by
  induction x using Ainf.toCoxeterSystem.simple_induction with
  | one => simp
  | simple i => grind [Ainf.shift_simple']
  | mul w i ih_w ih_i => simp [ih_w, ih_i]

lemma Ainf.shift_comp_shift (k k' : ℕ) :
    Ainf.shift k ∘ Ainf.shift k' = Ainf.shift (k + k') := by
  ext x
  apply Ainf.shift_shift

lemma AinfToPerm_shift_apply_lt (k : ℕ) (w_val : Ainf.Group) (i : ℕ) (hi : i < k) :
    AinfToPerm (Ainf.shift k w_val) i = i := by
  induction w_val using Ainf.toCoxeterSystem.simple_induction with
  | one => simp
  | simple j => grind [Ainf.shift_simple', AinfToPerm_simple]
  | mul w₁ w₂ ih_w₁ ih_w₂ => grind

lemma AinfToPerm_shift_apply_ge (k : ℕ) (w : Ainf.Group) (i : ℕ) (hi : k ≤ i) :
    AinfToPerm (Ainf.shift k w) i = k + AinfToPerm w (i - k) := by
  induction w using Ainf.toCoxeterSystem.simple_induction generalizing i with
  | one => grind
  | simple j => grind [Ainf.shift_simple', AinfToPerm_simple]
  | mul w₁ w₂ ih_w₁ ih_w₂ => grind

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

inductive monoidRelations : FreeMonoid B → FreeMonoid B → Prop
  | intro (i j : B) : monoidRelations ((.of i * .of j) ^ M i j) 1

protected def Monoid : Type _ := PresentedMonoid M.monoidRelations deriving Monoid

def monoidToGroup : M.Monoid →* M.Group :=
  PresentedMonoid.lift (fun x ↦ M.simple x) fun a b h => by
    cases h with | intro i j => simp [← CoxeterMatrix.toCoxeterSystem_simple]

@[simp]
lemma monoidToGroup_of (b : B) : M.monoidToGroup (PresentedMonoid.of _ b) = M.simple b := rfl

def groupToMonoid : M.Group →* M.Monoid :=
  M.toCoxeterSystem.lift ⟨(fun x ↦ .of _ x), fun i i' => by
    apply Quotient.sound
    dsimp
    constructor
    exact monoidRelations.intro _ _⟩

@[simp]
lemma groupToMonoid_simple (b : B) : M.groupToMonoid (M.simple b) = PresentedMonoid.of _ b := rfl

lemma monoidToGroupCompGroupToMonoid : M.monoidToGroup.comp M.groupToMonoid = .id _ := by
  apply M.toCoxeterSystem.ext_simple
  intro i
  rfl

lemma groupToMonoidCompMonoidToGroup : M.groupToMonoid.comp M.monoidToGroup = .id _ := by
  apply PresentedMonoid.ext
  intro i
  rfl

@[simp, grind =]
lemma monoidToGroup_groupToMonoid (x : M.Group) : M.monoidToGroup (M.groupToMonoid x) = x :=
  congr($(M.monoidToGroupCompGroupToMonoid) x)

@[simp, grind =]
lemma groupToMonoid_monoidToGroup (x : M.Monoid) : M.groupToMonoid (M.monoidToGroup x) = x :=
  congr($(M.groupToMonoidCompMonoidToGroup) x)

@[simps]
def monoidToGroupMulEquiv : M.Monoid ≃* M.Group where
  toFun := M.monoidToGroup
  invFun := M.groupToMonoid
  map_mul' := M.monoidToGroup.map_mul'
  left_inv x := by simp
  right_inv x := by simp

-- lemma monoidToGroupBijective

end CoxeterMatrix

/-- This is the submonoid of `FreeMonoid ℕ` spanned by generators `x` such that
`x < n + 1`. -/
def iioSubmonoidFreeMonoid (n : ℕ) : Submonoid (FreeMonoid ℕ) :=
  Submonoid.closure ((FreeMonoid.of)'' (Set.Iio n))

def iioSubmonoid (n : ℕ) : Submonoid (Ainf.Monoid) :=
  Submonoid.map (PresentedMonoid.mk _) (iioSubmonoidFreeMonoid n)

lemma of_mem_iioSubmonoidFreeMonoid_of_lt (n : ℕ) (j : ℕ) (hj : j < n) :
    FreeMonoid.of j ∈ iioSubmonoidFreeMonoid n :=
  Submonoid.mem_closure_of_mem <| Set.mem_image_of_mem _ hj

lemma of_mem_iioSubmonoid_of_lt (n : ℕ) (j : ℕ) (hj : j < n) :
    PresentedMonoid.of _ j ∈ iioSubmonoid n :=
  Submonoid.mem_map_of_mem _ <| Submonoid.mem_closure_of_mem <| Set.mem_image_of_mem _ hj

def AnToAinfMonoid (n : ℕ) : (CoxeterMatrix.Aₙ n).Monoid →* Ainf.Monoid :=
  Ainf.groupToMonoid.comp ((AnToAinf n).comp (CoxeterMatrix.Aₙ n).monoidToGroup)

@[simp]
lemma AnToAinfMonoid_of (n : ℕ) (j : Fin n) :
    AnToAinfMonoid n (.of ((CoxeterMatrix.Aₙ n).monoidRelations) j) = .of _ j.val := rfl

@[grind inj]
theorem injective_AinfToPerm : Function.Injective (AinfToPerm) := by
  intro u v huv
  obtain ⟨n, u₀, rfl⟩ := Ainf.exists_lift_to_Aₙ u
  obtain ⟨n', v₀, rfl⟩ := Ainf.exists_lift_to_Aₙ v
  wlog H : n ≤ n'
  · symm
    push_neg at H
    exact this _ _ _ _ huv.symm H.le
  · rw [← Aₙ.castLE_toAinf (h := H)] at huv ⊢
    simp only [MonoidHom.comp_apply] at huv ⊢
    congr 1
    apply injective_Aₙ_to_perm
    ext i
    have := congr($huv i)
    simpa [Aₙ_to_perm_apply_eq] using this

@[grind inj]
theorem injective_AnToAinf (n : ℕ) : Function.Injective (AnToAinf n) := by
  apply Function.Injective.of_comp (f := AinfToPerm)
  have :
    ⇑AinfToPerm ∘ ⇑(AnToAinf n) =
      (Equiv.Perm.extendDomainHom Fin.equivSubtype) ∘ ⇑(CoxeterMatrix.Aₙ_to_perm _) := by
    ext g x
    dsimp
    simpa using congr($(Aₙ_to_perm_extend _) g x).symm
  rw [this, Function.Injective.of_comp_iff]
  · exact injective_Aₙ_to_perm _
  · exact Equiv.Perm.extendDomainHom_injective _

theorem injective_AnToAinfMonoid (n : ℕ) : Function.Injective (AnToAinfMonoid n) := by
  dsimp [AnToAinfMonoid]
  rw [Function.Injective.of_comp_iff]
  · rw [Function.Injective.of_comp_iff]
    · exact (CoxeterMatrix.Aₙ n).monoidToGroupMulEquiv.injective
    · exact injective_AnToAinf _
  · exact Ainf.monoidToGroupMulEquiv.symm.injective

theorem image_AnToAinfMonoid (n : ℕ) :
    MonoidHom.mrange (AnToAinfMonoid n) = iioSubmonoid n := by
  rw [le_antisymm_iff]
  constructor
  · dsimp [iioSubmonoid]
    rw [MonoidHom.mrange_eq_map]
    have := PresentedMonoid.closure_range_of (CoxeterMatrix.Aₙ n).monoidRelations
    rw [← this, Submonoid.map_le_iff_le_comap, Submonoid.closure_le]
    rintro x ⟨y, rfl⟩
    use .of y.val, of_mem_iioSubmonoidFreeMonoid_of_lt _ _ y.prop
    rfl
  · dsimp [iioSubmonoid]
    rw [Submonoid.map_le_iff_le_comap, iioSubmonoidFreeMonoid, Submonoid.closure_le]
    rintro x ⟨y, hy, rfl⟩
    dsimp [Set.Iio] at hy
    use (.of _ ⟨y, hy⟩)
    rfl

abbrev AinfMonoidfToPerm : Ainf.Monoid →* Equiv.Perm ℕ :=
   AinfToPerm.comp Ainf.monoidToGroup

@[simp]
lemma AinfMonoidfToPerm_of (i : ℕ) :
    AinfMonoidfToPerm (PresentedMonoid.of _ i) = Equiv.swap i (i + 1) :=
  rfl
