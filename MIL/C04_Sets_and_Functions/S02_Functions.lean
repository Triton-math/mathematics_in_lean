import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  sorry

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  sorry

example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

-- 20260407 以上进度已完成 未存档

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, xs, rfl⟩, fxv⟩
    use x, ⟨xs, fxv⟩
  -- 善用rfl可以简短步骤
  rintro ⟨x, ⟨xs, x_sfinvv⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, x_sfinvv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro y ⟨x, ⟨xs, x_finvu⟩, rfl⟩
  exact ⟨⟨x, xs, rfl⟩, x_finvu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨xs, x_finvu⟩
  exact ⟨⟨x, xs, rfl⟩, x_finvu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs|x_finvu)
  · left
    exact ⟨x, xs, rfl⟩
  right
  exact x_finvu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  simp
  constructor
  · rintro ⟨x1, ⟨⟨i, x1Ai⟩, xfx1⟩⟩
    use i, x1
  · rintro ⟨i, ⟨x1, x1Ai, xfx1⟩⟩
    exact ⟨x1, ⟨⟨i, x1Ai⟩, xfx1⟩⟩

#print mem_sInter
#print mem_iInter
-- 注意一下，sInter是集合交集，而iInter是索引交集。前者的符号为 ∩₀，后者为 ∩
example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  rintro i x x_cap_Ai
  have xAi:= Set.mem_iInter.mp x_cap_Ai i
  use x

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg sxsy
  calc
    x = (sqrt x)^2 :=by rw[sq_sqrt x_nonneg]
    _ = (sqrt y)^2 :=by rw[sxsy]
    _ = y :=by rw[sq_sqrt y_nonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg x2y2
  simp at *
  have xpmy: (x-y)*(x+y)=0 :=by linarith[x2y2]
  rcases mul_eq_zero.mp xpmy with (xy|xnegy)
  · linarith[xy]
  linarith[xnegy, x_nonneg, y_nonneg]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext a; constructor
  · intro asqrtx
    rcases asqrtx with ⟨x, x_nonneg, rfl⟩
    exact sqrt_nonneg x
  intro a_nonneg
  use a^2
  constructor
  · apply sq_nonneg a
  simp at a_nonneg
  exact sqrt_sq a_nonneg

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext a
  simp; constructor
  · rintro ⟨y, rfl⟩
    apply sq_nonneg
  intro a_nonneg
  use sqrt a
  exact sq_sqrt a_nonneg

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  -- spec 是 Specification（规格/规范/特征）的缩写，给出一个【所选出的值的确满足既定要求】的证明。
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  -- dif_pos: Dependent IF postive, 用于改写inverse中的if
  -- 类似地，如果我们的条件是 ¬ (∃ x, f x = y)，那么我们应该使用 dif_neg
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

-- 可以使用 apply_fun 来对等式两边应用函数
example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

/- term模式 写法参考
example : Injective f ↔ LeftInverse (inverse f) f :=
  ⟨fun h y ↦ h (inverse_spec _ ⟨y, rfl⟩), fun h x1 x2 e ↦ by rw [← h x1, ← h x2, e]⟩
-/

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro fSur x
    rcases fSur x with h
    rw[inverse, dif_pos h]
    exact Classical.choose_spec h
  intro finvf_eqid x
  use inverse f x
  rw [finvf_eqid x]
end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := h ▸ h₁
  contradiction

-- COMMENTS: TODO: improve this
end
