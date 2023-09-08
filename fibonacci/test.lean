import Mathlib.Tactic

open Nat

-- フィボナッチ数列の評価中の式を構成する項
inductive Fdata where
   | F : Nat → Fdata
   -- フィボナッチ数同士の和
   | Fadd : Fdata → Fdata → Fdata
open Fdata

infixl:65   " +ᶠ " => Fadd

-- 項の中で評価が完了しているもの
inductive FValue : Fdata → Type where
   -- F 0
   | F0 : FValue (F 0)
   -- F 1
   | F1 : FValue (F 1)
   -- 評価が完了しているもの同士の和
   | FaddValue : ∀{M N}, FValue M → FValue N → FValue (M +ᶠ N)
open FValue

-- 評価が完了した項から自然数への関数
def value2nat : ∀{M}, (VM : FValue M) → Nat := fun VM ↦
   match VM with
   | F0 => 1
   | F1 => 1
   | FaddValue m n => (value2nat m) + (value2nat n)

#eval (value2nat (FaddValue (FaddValue F1 F0) F1))

-- 式の評価
-- 1段階の評価
inductive Freduce : Fdata → Fdata → Type where
   -- F n → F (n - 1) + F (n - 2), ただしn > 1
   | FaddIntro : ∀ n , n > 1
      → Freduce (F n) ((F (n - 1)) +ᶠ (F (n - 2)))
   -- F n + F m → L' + F m, ※F nがL'に評価できる場合
   | FreduceFirst : ∀ {L L' M}, Freduce L L'
      → Freduce (L +ᶠ M) (L' +ᶠ M)
   -- F n + F m → F n + M', ※F nがこれ以上評価できず、かつF mがM'に評価できる場合
   -- ここでF nに条件をくわえることで評価を決定的にしている
   | FreduceSecond : ∀ {L M M'}, FValue L → Freduce M M'
      → Freduce (L +ᶠ M) (L +ᶠ M')

infixr:75 "—→" => Freduce

-- 複数段階の評価
inductive Freduces : Fdata → Fdata → Type where
   -- 項が変化しない場合も評価とみなす
   | frfl : ∀ M , Freduces M M
   -- 1段階の評価と複数段階の評価は合成できる
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

-- 評価回数
-- 評価の状態（操作的な状態？）
inductive Fprogress (M : Fdata) where
   -- F nがまだ評価できる
   | step : ∀ {N}, M —→ N → Fprogress M
   -- これ以上評価できない
   | done : FValue M → Fprogress M
open Fprogress

#check (done F0)

theorem xadd2over2 : ∀ {x}, x + 2 > 1 := by
   intro x
   exact one_lt_succ_succ x

-- 項から評価状態の判定
def progress : (M : Fdata) → Fprogress M :=
  fun M ↦
  match M with
  -- 項がフィボナッチ数の単項の場合
   | F n =>
      match n with
      -- 引数の自然数が0, 1の場合は評価完了
      | 0 => done F0
      | 1 => done F1
      -- それ以上の場合は評価が可能
      | x + 2 => step (FaddIntro (x + 2) xadd2over2)
   -- 和で表されている場合
   | f1 +ᶠ f2 =>
      -- 左のオペランドの評価状態を確認する
      match (progress f1) with
      -- 評価可能である場合は式全体も評価可能
      | step fr1 => step (FreduceFirst fr1)
      -- 評価できない場合は右のオペランドについて確認する
      | done fv1 =>
         match (progress f2) with
         -- 評価可能である場合は式全体も評価可能
         | step f2reduce2f'2 => step (FreduceSecond fv1 f2reduce2f'2)
         -- 両方とも評価しきっている場合は評価完了
         | done fv2 => done (FaddValue fv1 fv2)

#check (progress (F 3))

-- 評価状態（表示的意味論な意味合い？）
inductive Finished (M : Fdata) where
   -- 評価が完了している
   | finish : FValue M → Finished M
   -- 評価が完了しなかった
   | outofgas : Finished M

open Finished

-- 式変形と評価結果
inductive Steps (M : Fdata) where
   | steps : ∀ {L},
      M —↠ L
      → Finished L
      → Steps M
open Steps

-- 与えられた上限までの間評価を行う
def evalFdata : Nat → (M : Fdata) → Steps M :=
   fun n M ↦
      match n with
      -- 0まで到達した場合は評価見完了
      | 0 => steps (M ∎) outofgas
      -- まだ上限に到達していない場合
      | (succ m) =>
         -- 現時点の評価状態を確認
         match (progress M) with
         -- 評価が完了している場合は終了とする
         | done fv => steps (M ∎) (finish fv)
         -- まだ評価可能な場合はさらに評価を行い、評価を合成する
         | step (N := N) Mreduces2N =>
            match (evalFdata m N) with
            | steps Nreduces2L fin => steps (M —↠⟨ Mreduces2N ⟩ Nreduces2L) fin

#check (evalFdata 10 (F 3))

-- 評価から自然数に変換
def evalSteps : ∀ {M}, Steps M → Nat :=
  fun sm ↦
  match sm with
  | steps _ fin =>
    match fin with
    -- 評価が完了している場合は変換
    | finish FV => value2nat FV
    -- 完了しなかった場合は0とする
    | outofgas => 0

#eval (evalSteps (evalFdata 21 (F 7)))
