-- Labels for the possible types of "high-level" terms.
inductive Ty
  | bool
  | nat

inductive Value : Ty → Type
  | bool : Bool → Value .bool
  | nat  : Nat  → Value .nat

instance : Coe Bool (Value .bool) where
  coe := .bool

-- A high-level language.
inductive Term : Ty → Type
  | val (v : Value τ)                          : Term τ
  | ite (cond : Term .bool) (pos neg : Term τ) : Term τ
  | and (lhs rhs : Term .bool)                 : Term .bool

namespace Term

instance : Coe (Value τ) (Term τ) where
  coe := val

-- An direct evaluation function on the high-level language.
def eval : Term τ → Value τ
  | val v => v
  | ite cond pos neg =>
    match eval cond with
    | true  => eval pos
    | false => eval neg
  | and lhs rhs =>
    match eval lhs, eval rhs with
    | true, true => true
    | _,    _    => false

@[simp]
theorem eval_val_eq_val (v : Value τ) : eval v = v := rfl

-- A restricted constant folding operation for high-level terms which only folds direct occurrences
-- of `and true true`, `and false true`, `and true false`, and `and false false`.
def constFold : Term τ → Term τ
  | val v                             => val v
  | ite cond pos neg                  => ite (constFold cond) (constFold pos) (constFold neg)
  | and true true                     => true
  | and (Value.bool _) (Value.bool _) => false
  | and lhs rhs                       => and (constFold lhs) (constFold rhs)

-- Two terms are considered equivalent if they evaluate to the same value.
def Equiv (t₁ t₂ : Term τ) : Prop :=
  eval t₁ = eval t₂

namespace Equiv

infixl:50 " ~ " => Equiv

-- `~` is a congruence with respect to `ite`.
theorem ite_congr (hc : c₁ ~ c₂) (hp : p₁ ~ p₂) (hn : n₁ ~ n₂) : ite c₁ p₁ n₁ ~ ite c₂ p₂ n₂ := by
  rw [Equiv, eval, eval, hc, hp, hn]

-- `~` is a congruence with respect to `and`.
theorem and_congr (hl : l₁ ~ l₂) (hr : r₁ ~ r₂) : and l₁ r₁ ~ and l₂ r₂ := by
  rw [Equiv, eval, eval, hl, hr]

@[simp]
theorem and_true : and true true ~ true := rfl

@[simp]
theorem and_false (h : b₁ = false ∨ b₂ = false) : and b₁ b₂ ~ false := by
  cases h <;> simp only [*, Equiv, eval]

end Equiv

-- Constant folding is semantics preserving.
theorem constFold_equiv (t : Term τ) : t ~ constFold t := by
  induction t
  case val v => rfl
  case ite hc hp hn => exact Equiv.ite_congr hc hp hn
  case and lhs rhs hl hr =>
    unfold constFold
    cases lhs <;> cases rhs
    case val.val v₁ v₂ => cases v₁; cases v₂; cases ‹Bool› <;> cases ‹Bool› <;> simp
    all_goals simp only [Equiv.and_congr hl hr]

end Term

open Term (eval)

-- An instruction in the stack machine.
inductive Instruction
  | const (n : Nat)
  | and
  | jmp (offset : Nat)
  | jez (offset : Nat)

abbrev Program := List Instruction

abbrev Stack := List Nat

-- A notion of conjunction over natural numbers.
def Nat.conj : Nat → Nat → Nat
  | 0, _ | _, 0 => 0
  | _, _        => 1

-- When executing an instruction we return an `Instruction.Result` consisting of an updated stack
-- and a jump-offset.
structure Instruction.Result where
  stack : Stack
  offset := 0

-- The implementation for executing a single instruction.
--
-- Note: An offset of 0 means that after this instruction we simply process the next instruction.
--       If it's 1, we skip the next instruction.
def Instruction.exec : Instruction → Stack → Option Instruction.Result
  | .const n,    stack        => some { stack := n :: stack }
  | .and,        r :: l :: tl => some { stack := (l.conj r) :: tl }
  | .and,        _            => none
  | .jmp offset, stack        => some { stack, offset }
  | .jez offset, 0 :: tl      => some { stack := tl, offset }
  | .jez _,      _ :: tl      => some { stack := tl }
  | .jez _,      _            => none

namespace Program

-- Returns the program obtained by jumping forward by a given number of instructions. If the
-- jump-offset exceeds the length of the program `none` is returned.
def goto : Program → Nat → Option Program
  | prog,    0          => prog
  | [],      _ + 1      => none
  | _ :: tl, offset + 1 => goto tl offset

-- Jumping forward in a program decreases its length.
theorem goto_decreasing {p : Program} (h : p.goto offset = some p') : p'.length ≤ p.length := by
  induction p generalizing offset <;> cases offset <;> simp_all [goto]
  case cons.succ hi _ => exact Nat.le_succ_of_le (hi h)

-- The execution function for a given stack machine program.
set_option linter.unusedVariables false in
def exec : Program → Stack → Option Stack
  | [],       stack => stack
  | hd :: tl, stack =>
    match Instruction.exec hd stack with
    | none => none
    | some { stack, offset } =>
      match h : goto tl offset with
      | none   => none
      | some p => exec p stack
termination_by p => p.length
decreasing_by simp +arith [goto_decreasing h]

end Program

-- Natural number semantics of high-level values.
def Value.toNat : Value τ → Nat
  | bool false => 0
  | bool true  => 1
  | nat n      => n

-- Lowers terms from the high-level language to stack machine programs.
def Term.lower : Term τ → Program
  | val v            => [.const v.toNat]
  | and lhs rhs      => (lower lhs) ++ (lower rhs) ++ [.and]
  | ite cond pos neg =>
    let p := lower pos
    let n := lower neg
    lower cond ++ [.jez (p.length + 1)] ++ p ++ [.jmp n.length] ++ n

-- (Heterogeneous) equivalence between a high-level term and a stack machine program.
-- This is the core notion of semantic preservation for lowering and, thus, for the compiler.
def HEquiv (t : Term τ) (prog : Program) : Prop :=
  prog.exec [] = some [t.eval.toNat]

infixl:60 " ≈ " => HEquiv

-- Equivalence is a congruence with respect to heterogeneous equivalence.
theorem HEquiv.equiv_congr (ht : t₁ ~ t₂) (hp : t₁ ≈ prog) : t₂ ≈ prog := by
  rw [HEquiv, ←ht, hp]

namespace Instruction

@[simp]
theorem jmp_def (offset s) : exec (.jmp offset) s = some ⟨s, offset⟩ := rfl

@[simp]
theorem jez_zero (offset s) : exec (.jez offset) (0 :: s) = some ⟨s, offset⟩ := rfl

@[simp]
theorem jez_succ (n offset s) : exec (.jez offset) ((n + 1) :: s) = some ⟨s, 0⟩ := rfl

-- If executing an instruction on a stack `s₁` yields a given result, then executing the same
-- instruction on a stack `s₁ ++ s` yields the same result with `s` glued to the bottom.
@[simp]
theorem exec_stack_mono (s : Stack) (h : exec inst s₁ = some ⟨s₂, o⟩) :
    exec inst (s₁ ++ s) = some ⟨s₂ ++ s, o⟩ := by
  cases inst
  case const => injection h with h; injection h with h₁ h₂; simp [exec, h₂, ←h₁]
  case and =>
    cases s₁ <;> try cases ‹Stack› <;> try contradiction
    injection h with h; injection h with h₁ h₂; simp [exec, ←h₁, h₂]
  case jmp => simp_all [exec]
  case jez => cases s₁ <;> try cases ‹Nat› <;> simp_all [exec]

end Instruction

namespace Program

-- Jumping by an offset of `0` yields the same program.
@[simp]
theorem goto_zero (prog : Program) : goto prog 0 = some prog := by
  cases prog <;> rfl

-- Jumping by an offset `prog₁.length` for a program `prog₁ ++ prog₂` yields `prog₂`.
@[simp]
theorem goto_suffix (prog₁ prog₂ : Program) : goto (prog₁ ++ prog₂) prog₁.length = some prog₂ := by
  induction prog₁ generalizing prog₂ <;> simp_all [goto]

-- Jumping the entire length of the given program yields the empty program.
@[simp]
theorem goto_end {prog : Program} (h : offset = prog.length) : goto prog offset = some [] := by
  rw [←List.append_nil prog, h, goto_suffix]

-- If executing the head `i` of a program `i :: prog₁` yields an `offset` and stack `s₂`, then the
-- result is the same as running `prog₂` on `s₂`, where `prog₂` is the remaining program starting at
-- the offset.
theorem exec_goto (hi : i.exec s₁ = some ⟨s₂, offset⟩) (hg : goto prog₁ offset = some prog₂) :
    exec (i :: prog₁) s₁ = exec prog₂ s₂ := by
  simp only [exec, hi]; rw [hg]

-- If calling `goto` on a program `prog₁` yields a program `prog₁'`, then extending the program to
-- `prog₁ ++ prog₂` yields the same result with `prog₂` glued on the end.
theorem goto_mono (prog₂ : Program) (h : goto prog₁ offset = some prog₁') :
    goto (prog₁ ++ prog₂) offset = some (prog₁' ++ prog₂) := by
  induction prog₁, offset using goto.induct <;> simp_all [goto]

-- If executing a program on a stack `s₁` yields a given result, then executing the same
-- program on a stack `s₁ ++ s` yields the same result with `s` glued to the bottom.
@[simp]
theorem exec_stack_mono (s : Stack) (h : exec prog s₁ = some s₂) :
    exec prog (s₁ ++ s) = s₂ ++ s := by
  induction prog, s₁ using exec.induct <;> try (simp_all [exec]; done)
  next hh hg =>
    simp only [exec, hh] at h
    rw [hg] at h
    contradiction
  next hh _ hg hi =>
    simp only [exec, hh, Instruction.exec_stack_mono _ hh] at *
    rw [hg] at h ⊢
    exact hi h

-- If executing a program `p₁` on a stack `s₁` yields a stack `s₂`, then extending the program to
-- `p₁ ++ p₂` just means continuing execution with `p₂` on `s₂`.
@[simp]
theorem exec_prog_mono (prog₂ : Program) (h : exec prog₁ s₁ = some s₂) :
    exec (prog₁ ++ prog₂) s₁ = exec prog₂ s₂ := by
  induction prog₁, s₁ using exec.induct <;> try (simp_all [exec]; done)
  next hh hg =>
    simp only [exec, hh] at h
    rw [hg] at h
    contradiction
  next hh _ hg hi =>
    simp only [exec, hh, List.cons_append] at *
    rw [hg] at h
    rw [Program.goto_mono _ hg, ←(hi h)]

end Program

namespace Term

open Program List
open Instruction hiding exec

@[simp]
theorem toNat_conj_eq_eval_and_toNat (lhs rhs : Term .bool) :
    (and lhs rhs).eval.toNat = Nat.conj lhs.eval.toNat rhs.eval.toNat := by
  cases hl : eval lhs <;> cases hr : eval rhs
  cases ‹Bool› <;> cases ‹Bool› <;> simp only [eval, Nat.conj, Value.toNat, *]

theorem eq_false_of_toNat_eq_zero {v : Value .bool} (h : v.toNat = 0) : v = false := by
  cases v <;> cases ‹Bool› <;> simp_all [Value.toNat]

theorem eq_true_of_toNat_eq_succ {v : Value .bool} (h : v.toNat = n + 1) : v = true := by
  cases v <;> cases ‹Bool› <;> simp_all [Value.toNat]

-- Lowering a value is semantics preserving.
theorem lower_val_hEquiv (v : Value τ) : val v ≈ lower (val v) := by
  simp [HEquiv, lower, exec, goto, Instruction.exec]

-- Heterogeneous equivalence is a congruence with respect to conjunction.
theorem lower_and_hEquiv (hl : lhs ≈ lower lhs) (hr : rhs ≈ lower rhs) :
    and lhs rhs ≈ lower (and lhs rhs) := by
  have h₁ := exec_prog_mono (lower rhs ++ [.and]) hl
  have h₂ := exec_stack_mono [lhs.eval.toNat] hr
  simp only [nil_append, singleton_append] at h₂
  have h₃ := exec_prog_mono [.and] h₂
  simp [h₁, h₃, HEquiv, lower, exec, goto, Instruction.exec]

-- Heterogeneous equivalence is a congruence with respect to conditional statements.
theorem lower_ite_hEquiv {cond : Term .bool} {pos neg : Term τ}
    (hc : cond ≈ lower cond) (hp : pos ≈ lower pos) (hn : neg ≈ lower neg) :
    ite cond pos neg ≈ lower (ite cond pos neg) := by
  rw [HEquiv, lower, append_assoc, append_assoc, append_assoc] at *
  -- Give names to terms needed later.
  let pl    := pos.lower.length + 1
  let nl    := neg.lower.length
  let prog₃ := [.jmp nl] ++ neg.lower
  let prog₂ := pos.lower ++ prog₃
  let prog₁ := [.jez pl] ++ prog₂
  -- Peel off the leading `lower cond`.
  rw [exec_prog_mono prog₁ hc]
  -- Continue differently depending on what's on top of the stack.
  cases h : cond.eval.toNat
  case zero =>
    -- Peel off the leading `jez`.
    have hg := goto_suffix (pos.lower ++ [jmp nl]) neg.lower
    simp only [length_append, length_singleton, append_assoc] at hg
    have he := exec_goto (jez_zero pl []) hg
    simp only [prog₁, singleton_append, he]
    -- Close the goal by establishing that `eval` yields `neg.eval`.
    simp_all only [prog₂, prog₃, eval, eq_false_of_toNat_eq_zero h]
  case succ n =>
    -- Peel off the leading `jez`.
    have he := exec_goto (jez_succ n pl []) (goto_zero prog₂)
    simp only [prog₁, singleton_append, he]
    -- Peel off the leading `lower pos`.
    rw [exec_prog_mono prog₃ hp]
    -- Peel off the leading `jmp`.
    have he := exec_goto (jmp_def nl [pos.eval.toNat]) (goto_end rfl)
    simp only [prog₃, singleton_append, he]
    -- Close the goal by establishing that `eval` yields `pos.eval`.
    simp only [eval, exec, eq_true_of_toNat_eq_succ h]

-- Lowering is semantics preserving.
theorem lower_hEquiv (t : Term τ) : t ≈ lower t := by
  induction t
  case val          => exact lower_val_hEquiv _
  case and hl hr    => exact lower_and_hEquiv hl hr
  case ite hc hp hn => exact lower_ite_hEquiv hc hp hn

-- The definition of the compiler. It constant folds and then lowers to a stack machine program.
def compile (t : Term τ) : Program :=
  lower (constFold t)

-- Compilation is semantics preserving.
theorem semantic_preservation (t : Term τ) : t ≈ compile t :=
  (lower_hEquiv _).equiv_congr (constFold_equiv t).symm

end Term
