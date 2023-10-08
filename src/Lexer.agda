module Lexer where

open import Level
open import Level.Bounded using ([_])
open import Agda.Builtin.Nat using (_-_)

open import Data.Unit.Base using (⊤; tt)
open import Data.Bool
open import Data.Char.Base
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.String as String hiding (parens; length)
open import Data.String.Properties renaming (_≟_ to _≟str_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.List.Base as List using (List; _∷_; []; length)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Function.Base
open import Relation.Nullary using (yes; no)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Text.Parser.Position

--------------------------------------
-- Parameters for lexing

data Tok : Set where
  t-true       : Tok
  t-false      : Tok
  t-if         : Tok
  t-then       : Tok
  t-else       : Tok
  t-isZero     : Tok
  t-+          : Tok
  t-num        : ℕ → Tok
  t-λ          : Tok
  t-var        : String → Tok
  t-dot        : Tok

  t-:          : Tok  -- for type annotations
  t-ℕ          : Tok
  t-𝕃          : Tok
  t-→          : Tok
  t-⊤          : Tok
  t-⊥          : Tok
  t-×          : Tok
  t-⊎          : Tok
  t-List       : Tok
  t-Tree       : Tok
  t-Stream     : Tok
  t-Machine    : Tok

  t-triv       : Tok  -- products
  t-,          : Tok
  t-fst        : Tok
  t-snd        : Tok

  t-inl        : Tok  -- sums
  t-inr        : Tok
  t-case       : Tok
  t-or         : Tok

  t-∷          : Tok  -- lists
  t-nil        : Tok
  t-[          : Tok
  t-]          : Tok

  t-|          : Tok  -- trees, e.g. <a> | (<b> | <c>)
  t-<          : Tok
  t->          : Tok

  t-iteℕ       : Tok  -- iterators ite⊤ is left out, because its useless
  t-iteList    : Tok  --           if_then_else_ and case are used for Bools and Sums
  t-iteTree    : Tok

  t-head       : Tok  -- streams
  t-tail       : Tok
  t-genStream  : Tok

  t-put        : Tok  -- machines
  t-set        : Tok
  t-get        : Tok
  t-genMachine : Tok

  t-lpar       : Tok  -- parentheses
  t-rpar       : Tok

eq-tok : Decidable {A = Tok} _≡_
eq-tok t-true       t-true       = yes refl
eq-tok t-false      t-false      = yes refl
eq-tok t-if         t-if         = yes refl
eq-tok t-then       t-then       = yes refl
eq-tok t-else       t-else       = yes refl
eq-tok t-isZero     t-isZero     = yes refl
eq-tok t-+          t-+          = yes refl
eq-tok (t-num n) (t-num m) with n ≟ℕ m
... | yes eq = yes (cong t-num eq)
... | no ¬eq = no λ hyp → ¬eq (cong (λ { (t-num n) → n ; _ → 0}) hyp)
eq-tok t-λ t-λ = yes refl
eq-tok (t-var name) (t-var name') with name ≟str name'
... | yes eq = yes (cong t-var eq)
... | no ¬eq = no λ hyp → ¬eq (cong (λ { (t-var s) → s ; _ → ""}) hyp)
eq-tok t-dot        t-dot        = yes refl
eq-tok t-:          t-:          = yes refl
eq-tok t-ℕ          t-ℕ          = yes refl
eq-tok t-𝕃          t-𝕃          = yes refl
eq-tok t-→          t-→          = yes refl
eq-tok t-⊤          t-⊤          = yes refl
eq-tok t-⊥          t-⊥          = yes refl
eq-tok t-×          t-×          = yes refl
eq-tok t-⊎          t-⊎          = yes refl
eq-tok t-List       t-List       = yes refl
eq-tok t-Tree       t-Tree       = yes refl
eq-tok t-Stream     t-Stream     = yes refl
eq-tok t-Machine    t-Machine    = yes refl
eq-tok t-triv       t-triv       = yes refl
eq-tok t-,          t-,          = yes refl
eq-tok t-fst        t-fst        = yes refl
eq-tok t-snd        t-snd        = yes refl
eq-tok t-inl        t-inl        = yes refl
eq-tok t-inr        t-inr        = yes refl
eq-tok t-case       t-case       = yes refl
eq-tok t-or         t-or         = yes refl
eq-tok t-∷          t-∷          = yes refl
eq-tok t-nil        t-nil        = yes refl
eq-tok t-[          t-[          = yes refl
eq-tok t-]          t-]          = yes refl
eq-tok t-|          t-|          = yes refl
eq-tok t-<          t-<          = yes refl
eq-tok t->          t->          = yes refl
eq-tok t-iteℕ       t-iteℕ       = yes refl
eq-tok t-iteList    t-iteList    = yes refl
eq-tok t-iteTree    t-iteTree    = yes refl
eq-tok t-head       t-head       = yes refl
eq-tok t-tail       t-tail       = yes refl
eq-tok t-genStream  t-genStream  = yes refl
eq-tok t-put        t-put        = yes refl
eq-tok t-set        t-set        = yes refl
eq-tok t-get        t-get        = yes refl
eq-tok t-genMachine t-genMachine = yes refl
eq-tok t-lpar       t-lpar       = yes refl
eq-tok t-rpar       t-rpar       = yes refl
eq-tok _ _ = no no-more-eq where
  private postulate no-more-eq : ∀ {A} → A

Token : Set
Token = Position × Tok

keywords : List⁺ (String × Tok)
keywords = ("true"  , t-true)   ∷ ("false", t-false) ∷ ("if"    , t-if)     ∷ ("then"   , t-then)    ∷ ("else"   , t-else) ∷
           ("isZero", t-isZero) ∷ ("ℕ"    , t-ℕ)     ∷ ("𝕃"     , t-𝕃)      ∷ ("⊤"      , t-⊤)       ∷ ("⊥"      , t-⊥)    ∷
           ("List"  , t-List)   ∷ ("Tree" , t-Tree)  ∷ ("Stream", t-Stream) ∷ ("Machine", t-Machine) ∷ ("trivial", t-triv) ∷
           ("fst"   , t-fst)    ∷ ("snd"  , t-snd)   ∷ ("inl"   , t-inl)    ∷ ("inr"    , t-inr)     ∷ ("case"   , t-case) ∷
           ("or"    , t-or)     ∷ ("nil"  , t-nil)   ∷ ("iteℕ"  , t-iteℕ)   ∷ ("iteList", t-iteList) ∷ ("iteTree", t-iteTree) ∷
           ("head"  , t-head)   ∷ ("tail" , t-tail)  ∷ ("genStream" , t-genStream) ∷ ("put" , t-put) ∷ ("set", t-set) ∷
           ("get"   , t-get)    ∷ ("genMachine" , t-genMachine) ∷ []

breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤
breaking c = case c of λ where  -- whitespaces as well as symbols are separators between tokens
  '+'  → true , just t-+
  'λ'  → true , just t-λ
  '.'  → true , just t-dot
  ':'  → true , just t-:
  '→'  → true , just t-→
  '×'  → true , just t-×
  '⊎'  → true , just t-⊎
  ','  → true , just t-,
  '∷'  → true , just t-∷
  '['  → true , just t-[
  ']'  → true , just t-]
  '|'  → true , just t-|
  '<'  → true , just t-<
  '>'  → true , just t->
  '('  → true , just t-lpar
  ')'  → true , just t-rpar
  c    → if isSpace c then true , nothing else false , _

listch⇒ℕ : List Char → Maybe ℕ  -- note: leading zeros are ignored, i.e., "003042" ⇒ 3042
listch⇒ℕ [] = nothing
listch⇒ℕ = step 0 where
  step : ℕ → List Char → Maybe ℕ
  step n [] = just n
  step n (c ∷ cs) = if isDigit c then
                      step (n + (pow 10 (length cs)) * (toℕ c - 48)) cs
                    else
                      nothing where
    pow : ℕ → ℕ → ℕ
    pow b = λ { 0 → 1 ; (suc e) → b * (pow b e)}

default : String → Tok
default s = case (listch⇒ℕ (toList s)) of λ where
  (just n) → t-num n
  nothing  → t-var s  -- if not a keyword, check if it's a number, if not it's a var name

--------------------------------------
-- Examples (see: Tests/ for more)

private
  open import Text.Lexer keywords breaking default using (tokenize)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ : tokenize "λx.x" ≡ (record { line = 0 ; offset = 0 } , t-λ      ) ∷
                        (record { line = 0 ; offset = 1 } , t-var "x") ∷
                        (record { line = 0 ; offset = 2 } , t-dot    ) ∷
                        (record { line = 0 ; offset = 3 } , t-var "x") ∷ []
  _ = refl

  _ : tokenize " isZero (10+  foo)" ≡ (record { line = 0 ; offset =  1 } , t-isZero   ) ∷
                                      (record { line = 0 ; offset =  8 } , t-lpar     ) ∷
                                      (record { line = 0 ; offset =  9 } , t-num 10   ) ∷
                                      (record { line = 0 ; offset = 11 } , t-+        ) ∷
                                      (record { line = 0 ; offset = 14 } , t-var "foo") ∷
                                      (record { line = 0 ; offset = 17 } , t-rpar     ) ∷ []
  _ = refl

  _ : tokenize "if bar then 0 else 1" ≡ (start , t-if) ∷
                                        (record { line = 0 ; offset =  3 } , t-var "bar") ∷
                                        (record { line = 0 ; offset =  7 } , t-then     ) ∷
                                        (record { line = 0 ; offset = 12 } , t-num 0    ) ∷
                                        (record { line = 0 ; offset = 14 } , t-else     ) ∷
                                        (record { line = 0 ; offset = 19 } , t-num 1    ) ∷ []
  _ = refl
