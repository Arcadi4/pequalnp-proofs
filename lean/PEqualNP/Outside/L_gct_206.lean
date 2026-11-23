import Mathlib
import PEqualNP.Defs
noncomputable section

namespace PEqualNP.Outside

private abbrev KSub (m k : ℕ) := {S : Finset (Fin m) // S.card = k}

private def kSubMonoEquiv (m k : ℕ) : KSub m k ≃ {f : Fin k → Fin m // StrictMono f} where
  toFun S := ⟨fun a => S.1.orderEmbOfFin S.2 a, (S.1.orderEmbOfFin S.2).strictMono⟩
  invFun f := ⟨Finset.univ.map ⟨f.1, f.2.injective⟩, by simp⟩
  left_inv S := by
    apply Subtype.ext
    change Finset.univ.map (S.1.orderEmbOfFin S.2).toEmbedding = S.1
    exact Finset.map_orderEmbOfFin_univ S.1 S.2
  right_inv f := by
    apply Subtype.ext
    funext a
    exact (congrFun (Finset.orderEmbOfFin_unique
      (s := Finset.univ.map ⟨f.1, f.2.injective⟩) (by simp) (by intro b; simp) f.2) a).symm

private theorem sumKSub_eq_sumMono (m k : ℕ) (F : (Fin k → Fin m) → ℂ) :
    (∑ S : KSub m k, F (fun a => S.1.orderEmbOfFin S.2 a)) =
      ∑ f : {f : Fin k → Fin m // StrictMono f}, F f.1 := by
  rw [Fintype.sum_equiv (kSubMonoEquiv m k) (fun S => F (fun a => S.1.orderEmbOfFin S.2 a))
    (fun f => F f.1)]
  intro S
  rfl

private theorem sumMono_eq_sumFun (k m : ℕ) (F : (Fin k → Fin m) → ℂ)
    (hF : ∀ f : Fin k → Fin m, ¬ StrictMono f → F f = 0) :
    (∑ f : {f : Fin k → Fin m // StrictMono f}, F f.1) = ∑ f : Fin k → Fin m, F f := by
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun f : Fin k → Fin m => StrictMono f) F
  have hzero : (∑ f : {f : Fin k → Fin m // ¬ StrictMono f}, F f.1) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    exact hF f.1 f.2
  rw [← hsub, hzero, add_zero]

private def arrowProd (α : Type) (k : ℕ) : (Fin (k + 1) → α) ≃ α × (Fin k → α) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    cases p
    ext i <;> rfl

private theorem sum_arrow_succ (α : Type) [Fintype α] (k : ℕ) (G : (Fin (k + 1) → α) → ℂ) :
    (∑ f : Fin (k + 1) → α, G f) = ∑ a : α, ∑ g : Fin k → α, G (Fin.cases a g) := by
  rw [Fintype.sum_equiv (arrowProd α k) G (fun p => G (Fin.cases p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro f
    change G f = G (Fin.cases (f 0) (fun i => f i.succ))
    have hf : (Fin.cases (f 0) (fun i => f i.succ) : Fin (k + 1) → α) = f := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    rw [hf]

private theorem sumFun_fin1 (α : Type) [Fintype α] (G : (Fin 1 → α) → ℂ) :
    (∑ f : Fin 1 → α, G f) = ∑ a : α, G ![a] := by
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) α) G (fun a => G ![a]) (by
    intro f
    congr 1
    funext i
    fin_cases i
    rfl)

private theorem sumFun_fin2 (α : Type) [Fintype α] (G : (Fin 2 → α) → ℂ) :
    (∑ f : Fin 2 → α, G f) = ∑ a : α, ∑ b : α, G ![a, b] := by
  rw [sum_arrow_succ α 1 G]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sumFun_fin1 α (fun g => G (Fin.cases a g))]
  apply Finset.sum_congr rfl
  intro b hb
  congr 1

private theorem sumFun_fin3 (α : Type) [Fintype α] (G : (Fin 3 → α) → ℂ) :
    (∑ f : Fin 3 → α, G f) = ∑ a : α, ∑ b : α, ∑ c : α, G ![a, b, c] := by
  rw [sum_arrow_succ α 2 G]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sumFun_fin2 α (fun g => G (Fin.cases a g))]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  congr 1

private theorem sumFun_fin4 (α : Type) [Fintype α] (G : (Fin 4 → α) → ℂ) :
    (∑ f : Fin 4 → α, G f) = ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α, G ![a, b, c, d] := by
  rw [sum_arrow_succ α 3 G]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sumFun_fin3 α (fun g => G (Fin.cases a g))]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1

private def embInjEquiv (k n : ℕ) : (Fin k ↪ Fin n) ≃ {f : Fin k → Fin n // Function.Injective f} where
  toFun e := ⟨e, e.injective⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv e := by ext; rfl
  right_inv f := by ext; rfl

private theorem sumEmb_eq_sumFun (k n : ℕ) (G : (Fin k → Fin n) → ℂ)
    (hG : ∀ f : Fin k → Fin n, ¬ Function.Injective f → G f = 0) :
    (∑ e : Fin k ↪ Fin n, G e) = ∑ f : Fin k → Fin n, G f := by
  have hsub := Fintype.sum_subtype_add_sum_subtype (fun f : Fin k → Fin n => Function.Injective f) G
  have hzero : (∑ f : {f : Fin k → Fin n // ¬ Function.Injective f}, G f.1) = 0 := by
    apply Finset.sum_eq_zero
    intro f hf
    exact hG f.1 f.2
  have hfirst : (∑ f : {f : Fin k → Fin n // Function.Injective f}, G f.1) =
      ∑ e : Fin k ↪ Fin n, G e := by
    exact Fintype.sum_equiv (embInjEquiv k n).symm (fun f => G f.1) (fun e => G e) (fun _ => rfl)
  rw [← hfirst, ← hsub, hzero, add_zero]

private theorem inj_fin2 {α : Type} [DecidableEq α] (a b : α) :
    Function.Injective ![a, b] ↔ a ≠ b := by
  constructor
  · intro h hab
    exact (by decide : (0 : Fin 2) ≠ 1) (h (by simp [hab]))
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem inj_fin3 {α : Type} [DecidableEq α] (a b c : α) :
    Function.Injective ![a, b, c] ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro hab
      exact (by decide : (0 : Fin 3) ≠ 1) (h (by simp [hab]))
    · intro hac
      exact (by decide : (0 : Fin 3) ≠ 2) (h (by simp [hac]))
    · intro hbc
      exact (by decide : (1 : Fin 3) ≠ 2) (h (by simp [hbc]))
  · rintro ⟨hab, hac, hbc⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem inj_fin4 {α : Type} [DecidableEq α] (a b c d : α) :
    Function.Injective ![a, b, c, d] ↔ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hab; exact (by decide : (0 : Fin 4) ≠ 1) (h (by simp [hab]))
    · intro hac; exact (by decide : (0 : Fin 4) ≠ 2) (h (by simp [hac]))
    · intro had; exact (by decide : (0 : Fin 4) ≠ 3) (h (by simp [had]))
    · intro hbc; exact (by decide : (1 : Fin 4) ≠ 2) (h (by simp [hbc]))
    · intro hbd; exact (by decide : (1 : Fin 4) ≠ 3) (h (by simp [hbd]))
    · intro hcd; exact (by decide : (2 : Fin 4) ≠ 3) (h (by simp [hcd]))
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem strictMono_fin2 {α : Type} [Preorder α] (a b : α) :
    StrictMono ![a, b] ↔ a < b := by
  constructor
  · intro h
    exact h (by decide : (0 : Fin 2) < 1)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem strictMono_fin3 {α : Type} [Preorder α] (a b c : α) :
    StrictMono ![a, b, c] ↔ a < b ∧ b < c := by
  constructor
  · intro h
    exact ⟨h (by decide : (0 : Fin 3) < 1), h (by decide : (1 : Fin 3) < 2)⟩
  · rintro ⟨hab, hbc⟩ i j hij
    have hac : a < c := lt_trans hab hbc
    fin_cases i <;> fin_cases j <;> simp_all

private theorem strictMono_fin4 {α : Type} [Preorder α] (a b c d : α) :
    StrictMono ![a, b, c, d] ↔ a < b ∧ b < c ∧ c < d := by
  constructor
  · intro h
    exact ⟨h (by decide : (0 : Fin 4) < 1), h (by decide : (1 : Fin 4) < 2),
      h (by decide : (2 : Fin 4) < 3)⟩
  · rintro ⟨hab, hbc, hcd⟩ i j hij
    have hac : a < c := lt_trans hab hbc
    have had : a < d := lt_trans hac hcd
    have hbd : b < d := lt_trans hbc hcd
    fin_cases i <;> fin_cases j <;> simp_all

private def embK {m k : ℕ} (S : KSub m k) (σ : Equiv.Perm (Fin k)) : Fin k ↪ Fin m :=
  ⟨fun a => S.1.orderEmbOfFin S.2 (σ a), (S.1.orderEmbOfFin S.2).injective.comp σ.injective⟩

private theorem range_embK {m k : ℕ} (S : KSub m k) (σ : Equiv.Perm (Fin k)) :
    Set.range (embK S σ) = (S.1 : Set (Fin m)) := by
  change Set.range ((S.1.orderEmbOfFin S.2) ∘ σ) = _
  rw [σ.surjective.range_comp, Finset.range_orderEmbOfFin]

private theorem embK_bijective (m k : ℕ) :
    Function.Bijective (fun p : KSub m k × Equiv.Perm (Fin k) => embK p.1 p.2) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    change embK S σ = embK T τ at h
    have hST : S = T := by
      apply Subtype.ext
      apply Finset.coe_injective
      rw [← range_embK S σ, ← range_embK T τ, h]
    subst hST
    have hστ : σ = τ := by
      ext b
      have := DFunLike.congr_fun h b
      exact congrArg Fin.val ((S.1.orderEmbOfFin S.2).injective this)
    rw [hστ]
  · intro i
    let S : KSub m k := ⟨Finset.univ.map i, by simp⟩
    have hmem : ∀ b, i b ∈ S.1 := fun b => by simp [S]
    let f : Fin k → Fin k := fun b => (S.1.orderIsoOfFin S.2).symm ⟨i b, hmem b⟩
    have hf : Function.Injective f := by
      intro b c hbc
      have := congrArg (fun x => ((S.1.orderIsoOfFin S.2 x : S.1) : Fin m)) hbc
      simp only [f, OrderIso.apply_symm_apply] at this
      exact i.injective this
    refine ⟨(S, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)), ?_⟩
    ext b
    simp only [embK, Function.Embedding.coeFn_mk, Equiv.ofBijective_apply]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp [f]


private theorem inj_fin1 {α : Type} (a : α) : Function.Injective ![a] := by
  intro i j hij
  fin_cases i
  fin_cases j
  rfl
private theorem sumEmbK (m k : ℕ) (F : (Fin k ↪ Fin m) → ℂ) :
    ∑ i, F i = ∑ S : KSub m k, ∑ σ : Equiv.Perm (Fin k), F (embK S σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (embK_bijective m k) (fun p => F (embK p.1 p.2)) F
    (fun _ => rfl)).symm

private noncomputable def mkRect (m n k : ℕ) (t : Fin m × Fin n → ℂ) : ℂ :=
  ∑ S : KSub m k, ∑ T : KSub n k,
    Matrix.permanent (Matrix.of fun a b : Fin k => t (S.1.orderEmbOfFin S.2 a, T.1.orderEmbOfFin T.2 b))

private theorem sumKSub_perm_eq_emb (n k : ℕ) (M : Fin k × Fin n → ℂ) :
    (∑ T : KSub n k, Matrix.permanent (Matrix.of fun a b : Fin k => M (a, T.1.orderEmbOfFin T.2 b))) =
      ∑ e : Fin k ↪ Fin n, ∏ a, M (a, e a) := by
  rw [sumEmbK n k (fun e => ∏ a, M (a, e a))]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  rfl

private theorem mkRowsEmb (m n k : ℕ) (t : Fin m × Fin n → ℂ) :
    mkRect m n k t = ∑ S : KSub m k, ∑ e : Fin k ↪ Fin n, ∏ a, t (S.1.orderEmbOfFin S.2 a, e a) := by
  unfold mkRect
  apply Finset.sum_congr rfl
  intro S hS
  exact sumKSub_perm_eq_emb n k (fun p => t (S.1.orderEmbOfFin S.2 p.1, p.2))

private theorem mk2 (t : Fin 4 × Fin 6 → ℂ) :
    mkRect 4 6 2 t =
      ∑ a : Fin 4, ∑ b : Fin 4, if a < b then
        ∑ j : Fin 6, ∑ l : Fin 6, if j ≠ l then t (a, j) * t (b, l) else 0
      else 0 := by
  rw [mkRowsEmb]
  rw [sumKSub_eq_sumMono 4 2 (fun r => ∑ e : Fin 2 ↪ Fin 6, ∏ a, t (r a, e a))]
  rw [show (∑ r : {r : Fin 2 → Fin 4 // StrictMono r}, ∑ e : Fin 2 ↪ Fin 6, ∏ a, t (r.1 a, e a)) =
      ∑ r : {r : Fin 2 → Fin 4 // StrictMono r},
        if hr : StrictMono r.1 then ∑ e : Fin 2 ↪ Fin 6, ∏ a, t (r.1 a, e a) else 0 by
    apply Finset.sum_congr rfl
    intro r hr
    simp [r.2]]
  rw [sumMono_eq_sumFun 2 4 (fun r => if hr : StrictMono r then
    ∑ e : Fin 2 ↪ Fin 6, ∏ a, t (r a, e a) else 0) (by
      intro r hr
      simp [hr])]
  rw [sumFun_fin2]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a < b
  · have hs : StrictMono ![a, b] := (strictMono_fin2 a b).2 hab
    rw [dif_pos hs]
    simp only [hab, if_true]
    rw [show (∑ e : Fin 2 ↪ Fin 6, ∏ x, t (![a, b] x, e x)) =
        ∑ e : Fin 2 ↪ Fin 6, if he : Function.Injective (e : Fin 2 → Fin 6) then
          ∏ x, t (![a, b] x, e x) else 0 by
      apply Finset.sum_congr rfl
      intro e he
      simp [e.injective]]
    rw [sumEmb_eq_sumFun 2 6 (fun f => if hf : Function.Injective f then
      ∏ x, t (![a, b] x, f x) else 0) (by
        intro f hf
        simp [hf])]
    rw [sumFun_fin2]
    simp [inj_fin2]
  · have hs : ¬ StrictMono ![a, b] := fun h => hab ((strictMono_fin2 a b).1 h)
    rw [dif_neg hs]
    simp [hab]

private theorem mk3 (t : Fin 4 × Fin 6 → ℂ) :
    mkRect 4 6 3 t =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then
        ∑ j : Fin 6, ∑ l : Fin 6, ∑ m : Fin 6,
          if j ≠ l ∧ j ≠ m ∧ l ≠ m then t (a, j) * t (b, l) * t (c, m) else 0
      else 0 := by
  rw [mkRowsEmb]
  rw [sumKSub_eq_sumMono 4 3 (fun r => ∑ e : Fin 3 ↪ Fin 6, ∏ a, t (r a, e a))]
  rw [show (∑ r : {r : Fin 3 → Fin 4 // StrictMono r}, ∑ e : Fin 3 ↪ Fin 6, ∏ a, t (r.1 a, e a)) =
      ∑ r : {r : Fin 3 → Fin 4 // StrictMono r},
        if hr : StrictMono r.1 then ∑ e : Fin 3 ↪ Fin 6, ∏ a, t (r.1 a, e a) else 0 by
    apply Finset.sum_congr rfl
    intro r hr
    simp [r.2]]
  rw [sumMono_eq_sumFun 3 4 (fun r => if hr : StrictMono r then
    ∑ e : Fin 3 ↪ Fin 6, ∏ a, t (r a, e a) else 0) (by
      intro r hr
      simp [hr])]
  rw [sumFun_fin3]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  by_cases habc : a < b ∧ b < c
  · have hs : StrictMono ![a, b, c] := (strictMono_fin3 a b c).2 habc
    rw [dif_pos hs]
    simp only [habc, if_true]
    rw [show (∑ e : Fin 3 ↪ Fin 6, ∏ x, t (![a, b, c] x, e x)) =
        ∑ e : Fin 3 ↪ Fin 6, if he : Function.Injective (e : Fin 3 → Fin 6) then
          ∏ x, t (![a, b, c] x, e x) else 0 by
      apply Finset.sum_congr rfl
      intro e he
      simp [e.injective]]
    rw [sumEmb_eq_sumFun 3 6 (fun f => if hf : Function.Injective f then
      ∏ x, t (![a, b, c] x, f x) else 0) (by
        intro f hf
        simp [hf])]
    rw [sumFun_fin3]
    simp [inj_fin3, Fin.prod_univ_three]
  · have hs : ¬ StrictMono ![a, b, c] := fun h => habc ((strictMono_fin3 a b c).1 h)
    rw [dif_neg hs]
    simp [habc]

private theorem mk4 (t : Fin 4 × Fin 6 → ℂ) :
    mkRect 4 6 4 t =
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4,
        if a < b ∧ b < c ∧ c < d then
          ∑ j : Fin 6, ∑ l : Fin 6, ∑ m : Fin 6, ∑ n : Fin 6,
            if j ≠ l ∧ j ≠ m ∧ j ≠ n ∧ l ≠ m ∧ l ≠ n ∧ m ≠ n then
              t (a, j) * t (b, l) * t (c, m) * t (d, n)
            else 0
        else 0 := by
  rw [mkRowsEmb]
  rw [sumKSub_eq_sumMono 4 4 (fun r => ∑ e : Fin 4 ↪ Fin 6, ∏ a, t (r a, e a))]
  rw [show (∑ r : {r : Fin 4 → Fin 4 // StrictMono r}, ∑ e : Fin 4 ↪ Fin 6, ∏ a, t (r.1 a, e a)) =
      ∑ r : {r : Fin 4 → Fin 4 // StrictMono r},
        if hr : StrictMono r.1 then ∑ e : Fin 4 ↪ Fin 6, ∏ a, t (r.1 a, e a) else 0 by
    apply Finset.sum_congr rfl
    intro r hr
    simp [r.2]]
  rw [sumMono_eq_sumFun 4 4 (fun r => if hr : StrictMono r then
    ∑ e : Fin 4 ↪ Fin 6, ∏ a, t (r a, e a) else 0) (by
      intro r hr
      simp [hr])]
  rw [sumFun_fin4]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  by_cases habcd : a < b ∧ b < c ∧ c < d
  · have hs : StrictMono ![a, b, c, d] := (strictMono_fin4 a b c d).2 habcd
    rw [dif_pos hs]
    simp only [habcd, if_true]
    rw [show (∑ e : Fin 4 ↪ Fin 6, ∏ x, t (![a, b, c, d] x, e x)) =
        ∑ e : Fin 4 ↪ Fin 6, if he : Function.Injective (e : Fin 4 → Fin 6) then
          ∏ x, t (![a, b, c, d] x, e x) else 0 by
      apply Finset.sum_congr rfl
      intro e he
      simp [e.injective]]
    rw [sumEmb_eq_sumFun 4 6 (fun f => if hf : Function.Injective f then
      ∏ x, t (![a, b, c, d] x, f x) else 0) (by
        intro f hf
        simp [hf])]
    rw [sumFun_fin4]
    simp [inj_fin4, Fin.prod_univ_four]
  · have hs : ¬ StrictMono ![a, b, c, d] := fun h => habcd ((strictMono_fin4 a b c d).1 h)
    rw [dif_neg hs]
    simp [habcd]

private theorem ifsum_eq_subsum (m n k : ℕ) (t : Fin m × Fin n → ℂ) :
    (∑ R : Finset (Fin m), ∑ C : Finset (Fin n),
      if h : R.card = k ∧ C.card = k then
        Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
      else 0)
    = mkRect m n k t := by
  classical
  unfold mkRect
  let F : Finset (Fin m) × Finset (Fin n) → ℂ := fun p =>
    if h : p.1.card = k ∧ p.2.card = k then
      Matrix.permanent (Matrix.of fun a b => t (p.1.orderEmbOfFin h.1 a, p.2.orderEmbOfFin h.2 b))
    else 0
  let G : KSub m k × KSub n k → ℂ := fun q =>
    Matrix.permanent (Matrix.of fun a b => t (q.1.1.orderEmbOfFin q.1.2 a, q.2.1.orderEmbOfFin q.2.2 b))
  let e : {p : Finset (Fin m) × Finset (Fin n) // p.1.card = k ∧ p.2.card = k} ≃
      (KSub m k × KSub n k) :=
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun q => ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩
      left_inv := by intro p; ext <;> rfl
      right_inv := by intro q; ext <;> rfl }
  have hprodF : (∑ p : Finset (Fin m) × Finset (Fin n), F p) =
      ∑ R : Finset (Fin m), ∑ C : Finset (Fin n), F (R, C) := by
    simpa using (Fintype.sum_prod_type F)
  have hprodG : (∑ q : KSub m k × KSub n k, G q) =
      ∑ S : KSub m k, ∑ T : KSub n k, G (S, T) := by
    simpa using (Fintype.sum_prod_type G)
  rw [← hprodF, ← hprodG]
  have hsub := Fintype.sum_subtype_add_sum_subtype
    (fun p : Finset (Fin m) × Finset (Fin n) => p.1.card = k ∧ p.2.card = k) F
  have hzero : (∑ p : {p : Finset (Fin m) × Finset (Fin n) //
      ¬ (p.1.card = k ∧ p.2.card = k)}, F p.1) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [F, p.2]
  rw [← hsub, hzero, add_zero]
  rw [Fintype.sum_equiv e (fun p => F p.1) G]
  intro p
  simp [F, G, e, p.2]

private def entries (z : ℂ) (x : Fin 7 → ℂ) (p : Fin 4 × Fin 6) : ℂ :=
  ![![x 0, x 1, x 2, x 3, x 4, -(x 0 + x 1 + x 2 + x 3 + x 4)],
    ![x 5, -x 5, x 6, -x 6, 0, 0],
    ![z * x 5, -(z * x 5), z ^ 2 * x 6, -(z ^ 2 * x 6), 0, 0],
    ![z ^ 2 * x 5, -(z ^ 2 * x 5), z * x 6, -(z * x 6), 0, 0]] p.1 p.2

private def family (z : ℂ) : (Fin 7 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 6 → ℂ) where
  toFun := entries z
  map_add' x y := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries, mul_add] <;> ring
  map_smul' c x := by
    funext ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> simp [entries] <;> ring

private theorem family_injective (z : ℂ) : Function.Injective (family z) := by
  intro x y h
  let positions : Fin 7 → Fin 4 × Fin 6 :=
    ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 2)]
  funext k
  have hk := congrFun h (positions k)
  fin_cases k <;> exact hk

private theorem row_sum (z : ℂ) (x : Fin 7 → ℂ) (i : Fin 4) :
    ∑ j, entries z x (i, j) = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_six, entries]

private theorem mk1 (t : Fin 4 × Fin 6 → ℂ) :
    mkRect 4 6 1 t = ∑ i : Fin 4, ∑ j : Fin 6, t (i, j) := by
  rw [mkRowsEmb]
  rw [sumKSub_eq_sumMono 4 1 (fun r => ∑ e : Fin 1 ↪ Fin 6, ∏ a, t (r a, e a))]
  rw [show (∑ r : {r : Fin 1 → Fin 4 // StrictMono r}, ∑ e : Fin 1 ↪ Fin 6, ∏ a, t (r.1 a, e a)) =
      ∑ r : {r : Fin 1 → Fin 4 // StrictMono r},
        if hr : StrictMono r.1 then ∑ e : Fin 1 ↪ Fin 6, ∏ a, t (r.1 a, e a) else 0 by
    apply Finset.sum_congr rfl
    intro r hr
    simp [r.2]]
  rw [sumMono_eq_sumFun 1 4 (fun r => if hr : StrictMono r then
    ∑ e : Fin 1 ↪ Fin 6, ∏ a, t (r a, e a) else 0) (by
      intro r hr
      simp [hr])]
  rw [sumFun_fin1]
  apply Finset.sum_congr rfl
  intro a ha
  rw [dif_pos (by
    intro i j hij
    omega)]
  rw [show (∑ e : Fin 1 ↪ Fin 6, ∏ x, t (![a] x, e x)) =
      ∑ e : Fin 1 ↪ Fin 6, if he : Function.Injective (e : Fin 1 → Fin 6) then
        ∏ x, t (![a] x, e x) else 0 by
    apply Finset.sum_congr rfl
    intro e he
    simp [e.injective]]
  rw [sumEmb_eq_sumFun 1 6 (fun f => if hf : Function.Injective f then
    ∏ x, t (![a] x, f x) else 0) (by
      intro f hf
      simp [hf])]
  rw [sumFun_fin1]
  simp [inj_fin1]

set_option maxHeartbeats 2000000 in
private theorem mk1_entries (z : ℂ) (x : Fin 7 → ℂ) : mkRect 4 6 1 (entries z x) = 0 := by
  rw [mk1]
  simp [Fin.sum_univ_four, row_sum z x]

set_option maxHeartbeats 4000000 in
private theorem mk2_entries (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    mkRect 4 6 2 (entries z x) = 0 := by
  rw [mk2]
  simp (config := { decide := true }) [Fin.sum_univ_six, Fin.sum_univ_four, entries]
  grobner

set_option maxHeartbeats 4000000 in
private theorem mk3_entries (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    mkRect 4 6 3 (entries z x) = 0 := by
  rw [mk3]
  simp (config := { decide := true }) [Fin.sum_univ_six, Fin.sum_univ_four, entries]
  grobner

set_option maxHeartbeats 8000000 in
private theorem mk4_entries (z : ℂ) (hz : 1 + z + z ^ 2 = 0) (x : Fin 7 → ℂ) :
    mkRect 4 6 4 (entries z x) = 0 := by
  rw [mk4]
  simp (config := { decide := true }) [Fin.sum_univ_six, Fin.sum_univ_four, entries]
  grobner

theorem L_gct_206 :
    ∃ L : Submodule ℂ (Fin 4 × Fin 6 → ℂ), Module.finrank ℂ L = 7 ∧
      (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
        (∑ R : Finset (Fin 4), ∑ C : Finset (Fin 6),
          if h : R.card = k ∧ C.card = k then
            Matrix.permanent (Matrix.of fun a b =>
              t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b))
          else 0) = 0) := by
  obtain ⟨z, hprim⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot ℂ 3
  have hz : 1 + z + z ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using hprim.geom_sum_eq_zero (by decide)
  refine ⟨LinearMap.range (family z), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (family_injective z), Module.finrank_fin_fun]
  · rintro t ⟨x, rfl⟩ k hk1 hk4
    rw [ifsum_eq_subsum]
    interval_cases k
    · exact mk1_entries z x
    · exact mk2_entries z hz x
    · exact mk3_entries z hz x
    · exact mk4_entries z hz x

end PEqualNP.Outside
