import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]

section
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)
-- 尽管没有显式定义，但 f 与 g 被使用到，这体现在 sbAux 的类型中
#check sbAux

-- 定义全部的“圆环”为 sbSet
def sbSet :=
  ⋃ n, sbAux f g n
-- 相应地，sbSet 类型中也包含 f g
#check sbSet

-- 分段函数定义方式
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x


#print invFun
#print dif_pos
#print choose_spec
#print invFun_eq
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    constructor
    · trivial
    exact hx
  have Exy_xgy: ∃ y, g y = x := by
    rcases this with ⟨y, yuni, rfl⟩
    use y
  -- 可以直接使用 invFun_eq
  -- apply invFun_eq this
  -- 否则需要用 unfold 展开函数定义
  unfold invFun; rw[dif_pos Exy_xgy]
  apply choose_spec Exy_xgy

theorem wlog_test {x₁ x₂ : ℕ} (x1eqx2 : x₁ = x₂) (h : x₁ = 1 ∨ x₂ = 1) : (x₁ = 1 ∧ x₂ = 1) :=by
  -- wlog:P 的逻辑是：
  -- 1. 首先，假设我们**已经证明了只要P成立，整个命题就成立**。现在，我们来考虑**P不成立的情况**。
  -- 2. 然后，我们来处理，为什么当P成立的时候，整个命题就成立了。
  wlog x1eq1 : x₁ = 1 generalizing x₁ x₂ h
  -- Step 1
  · have x2eq1: x₂=1 :=by tauto
    symm
    apply this x1eqx2.symm h.symm x2eq1
  · constructor
    · exact x1eq1
    apply x1eqx2.symm.trans x1eq1

#print sb_right_inv
theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  -- 这里为什么要显式写出 hxeq？如果不显式写出，会影响后面的编译吗？
  -- BTW，发现了注释的快捷键：【command】+【/】
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  -- 展开 h，再使用 A_def 简化表达
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  -- 如何理解这里的 generalizing？它的意思是【泛化】。但，具体跟什么？逻辑是什么？语法又是什么？
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      -- _root_ 为路径指示符。若当前命名空间（Namespace）有同名的定义，使用 _root_ 可以确保调用的是**全局最顶层的定义**，而不是当前命名空间下的。
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        rw[hxeq]
        -- 似乎不需要使用定义改写，Lean4可以自动处理
        -- rw[A_def] at x₂nA
        symm
        apply sb_right_inv f g x₂nA
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw[if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
  push_neg at xA
  rcases xA with ⟨x₁A, x₂A⟩
  rw[if_neg x₁A, if_neg x₂A] at hxeq
  apply_fun (fun x↦ g x) at hxeq
  rw[sb_right_inv f g x₁A, sb_right_inv f g x₂A] at hxeq
  exact hxeq

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    -- 在底层定义中，自然数 n 或者是 0，或者是某个自然数 k 的后继 k+1
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]
    apply hg hx
  use g y
  rw[h_def, sbFun, if_neg gyA]
  unfold invFun
  have : ∃ x, g x = g y :=by use y
  -- 这一步用了 simp。只能如此吗？
  simp[this]
  apply hg; exact choose_spec this
end

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

-- Auxiliary information
section
variable (g : β → α) (x : α)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

end
