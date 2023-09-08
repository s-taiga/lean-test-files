import Mathlib.Tactic

open Nat

inductive Fdata where
   | F : Nat → Fdata
   | Fadd : Fdata → Fdata → Fdata
open Fdata

infixl:65   " +ᶠ " => Fadd

inductive FValue : Fdata → Type where
   | F0 : FValue (F 0)
   | F1 : FValue (F 1)
   | FaddValue : ∀{M N}, FValue M → FValue N → FValue (M +ᶠ N)
open FValue

def value2nat : ∀{M}, (VM : FValue M) → Nat := fun VM ↦
   match VM with
   | F0 => 1
   | F1 => 1
   | FaddValue m n => (value2nat m) + (value2nat n)

#eval (value2nat (FaddValue (FaddValue F1 F0) F1))

inductive Freduce : Fdata → Fdata → Type where
   | FaddIntro : ∀ n , n > 1
      → Freduce (F n) ((F (n - 1)) +ᶠ (F (n - 2)))
   | FreduceFirst : ∀ {L L' M}, Freduce L L'
      → Freduce (L +ᶠ M) (L' +ᶠ M)
   | FreduceSecond : ∀ {L M M'}, FValue L → Freduce M M'
      → Freduce (L +ᶠ M) (L +ᶠ M')

infixr:75 "—→" => Freduce

inductive Freduces : Fdata → Fdata → Type where
   | frfl : ∀ M , Freduces M M
   | ftrans : ∀ L {M N}, L —→ M → Freduces M N
      → Freduces L N

open Freduce
open Freduces

infixr:55 "—↠" => Freduces
notation:85 arg:85 "∎" => frfl arg
notation:95 L:95 "—↠⟨" Lreduce2M:95 "⟩" Mreduces2N => ftrans L Lreduce2M Mreduces2N

theorem p42 : 4 > 1 := by
   trivial
#check (FaddIntro 4 p42)

inductive Fprogress (M : Fdata) where
   | step : ∀ {N}, M —→ N → Fprogress M
   | done : FValue M → Fprogress M
open Fprogress

#check (done F0)

theorem xadd2over2 : ∀ {x}, x + 2 > 1 := by
   intro x
   exact one_lt_succ_succ x

def progress : (M : Fdata) → Fprogress M :=
  fun M ↦
  match M with
   | F n =>
      match n with
      | 0 => done F0
      | 1 => done F1
      | x + 2 => step (FaddIntro (x + 2) xadd2over2)
   | f1 +ᶠ f2 =>
      match (progress f1) with
      | step fr1 => step (FreduceFirst fr1)
      | done fv1 =>
         match (progress f2) with
         | step f2reduce2f'2 => step (FreduceSecond fv1 f2reduce2f'2)
         | done fv2 => done (FaddValue fv1 fv2)

#check (progress (F 3))

inductive Finished (M : Fdata) where
   | finish : FValue M → Finished M
   | outofgas : Finished M

open Finished

inductive Steps (M : Fdata) where
   | steps : ∀ {L},
      M —↠ L
      → Finished L
      → Steps M
open Steps

def evalFdata : Nat → (M : Fdata) → Steps M :=
   fun n M ↦
      match n with
      | 0 => steps (M ∎) outofgas
      | (succ m) =>
         match (progress M) with
         | done fv => steps (M ∎) (finish fv)
         | step (N := N) Mreduces2N =>
            match (evalFdata m N) with
            | steps Nreduces2L fin => steps (ftrans M Mreduces2N Nreduces2L) fin

#check (evalFdata 10 (F 3))

def evalSteps : ∀ {M}, Steps M → Nat :=
  fun sm ↦
  match sm with
  | steps _ fin =>
    match fin with
    | finish FV => value2nat FV
    | outofgas => 0

#eval (evalSteps (evalFdata 21 (F 7)))
