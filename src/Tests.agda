{-# OPTIONS --prop --rewriting --guardedness #-}

module Tests where

-- This module aims to be an extensive testing of the elaboration library
-- It also functions as a store of examples for the interested
--
-- If you wish to see all steps of an elaboration, run `elaborate <code>`
-- (for example, if you want to find out why something doesn't compile)
--
-- The amount of examples makes typechecking this file a little slow (5-10 secs), so it can be a
-- more pleasant experience to copy the imports to a new file and work there on new code

-- TODO: typechecking this file is quite slow, divide tests between different files instead
-- TODO: add more tests

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.String using (String; parens; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

_ : compile-eval "3" ≡ inj₁ (Nat , suco (suco (suco zeroo))
                                 , λ γ* → 3)
_ = refl
_ : compile-eval "isZero 2" ≡ inj₁ (Bool , iteNat true false (suco (suco zeroo))
                                         , λ γ* → ff)
_ = refl

_ : compile-eval "if isZero 0 then 1 else 0" ≡ inj₁ (Nat , iteBool (suco zeroo) zeroo (iteNat true false zeroo)
                                                         , λ γ* → 1)
_ = refl
_ : compile-eval "if isZero 1 then false else isZero 0" ≡ inj₁ (Bool , iteBool
                                                                         false
                                                                         (iteNat true false zeroo)
                                                                         (iteNat true false (suco zeroo))
                                                                     , λ γ* → tt)
_ = refl
_ : compile-eval "if true then 0 else false" ≡ inj₂ type-error -- branches have different types
_ = refl
_ : compile-eval "if 42 then 0 else 1"       ≡ inj₂ type-error -- condition is Nat instead of Bool
_ = refl
_ : compile-eval "λx.x"                      ≡ inj₂ type-error -- not annotated, type unknown
_ = refl
_ : compile-eval "10 true"                   ≡ inj₂ type-error -- application on non-function type
_ = refl
_ : compile-eval "(λx.x) : ℕ → ℕ"            ≡ inj₁ (Nat ⇒ Nat , lam q , λ γ* x → x)
_ = refl
_ : compile-eval "((λx.x) : ℕ → ℕ) 1 + 2" ≡ inj₁ (Nat , lam q $ (lam (lam (iteNat q (suco q) (q [ p ])))
                                                        $ suco zeroo $ suco (suco zeroo))
                                                      , λ γ* → 3)
_ = refl
_ : compile-eval "(λf. f true) : 𝕃 → ℕ → ℕ" ≡ inj₂ type-error -- → is right associative (we curry by default)
_ = refl
_ : compile-eval "(λf. f true) : (𝕃 → ℕ) → ℕ" ≡ inj₁ ((Bool ⇒ Nat) ⇒ Nat , lam (q $ true)
                                                                         , λ γ* f → f tt)
_ = refl
_ : compile-eval "(λ cond val. if cond then val else 0) : 𝕃 → ℕ → ℕ" ≡ inj₁ (Bool ⇒ Nat ⇒ Nat
                                                                          , lam (lam
                                                                            (iteBool q zeroo (q [ p ])))
                                                                          , λ γ* cond val → if cond then val else 0)
_ = refl

-- Products
_ : compile-eval "0 , false" ≡ inj₁ ((Nat ×o Bool) , ⟨ zeroo , false ⟩
                                                   , λ γ* → 0 , ff)
_ = refl
_ : compile-eval "trivial , 1 + 2 , ((λ x.x) : 𝕃 → 𝕃)" ≡ inj₁ ((Unit ×o (Nat ×o (Bool ⇒ Bool))) ,
                                                              ⟨ trivial , ⟨ lam (lam (iteNat q (suco q) (q [ p ])))
                                                              $ suco zeroo $ suco (suco zeroo) , lam q ⟩ ⟩
                                                            , λ γ* → _ , 3 , (λ x → x))
_ = refl

-- Sums
_ : compile-eval "inl 2" ≡ inj₂ type-error -- cannot deduce type
_ = refl
_ : compile-eval "(inl 2) : ℕ ⊎ ⊤" ≡ inj₁ ((Nat +o Unit) , inl (suco (suco zeroo))
                                                         , λ γ* → inj₁ 2)
_ = refl
_ : compile-eval "case ((λx.x):ℕ→ℕ) or ((λ_.0):⊤→ℕ)" ≡ inj₁ ((Nat +o Unit) ⇒ Nat ,
                                                            lam (caseo (lam q [ p ] $ q) (lam zeroo [ p ] $ q))
                                                          , λ γ* u → [ (λ x → x) , (λ _ → 0) ]′ u)
_ = refl
_ : compile-eval "(case ((λx.x):ℕ→ℕ) or ((λ_.0):⊤→ℕ)) inl 1" ≡ inj₁ (Nat , lam (caseo (lam q [ p ] $ q)
                                                                                      (lam zeroo [ p ] $ q))
                                                                               $ inl (suco zeroo)
                                                                         , λ γ* → 1)
_ = refl

-- Lists
_ : compile-eval "[0,1,2]"         ≡ inj₁ (Ty.List Nat , cons zeroo (cons (suco zeroo) (cons (suco (suco zeroo)) nil))
                                                       , λ γ* → 0 ∷ (1 ∷ (2 ∷ [])))
_ = refl
_ : compile-eval "0 ∷ 1 ∷ 2 ∷ nil" ≡ inj₁ (Ty.List Nat , cons zeroo (cons (suco zeroo) (cons (suco (suco zeroo)) nil))
                                                       , λ γ* → 0 ∷ (1 ∷ (2 ∷ [])))
_ = refl
_ : compile-eval "true ∷ (isZero 0)" ≡ inj₂ type-error -- 2nd operand to cons is not a list
_ = refl
_ : compile-eval "[1, trivial]"      ≡ inj₂ type-error -- different type of elements
_ = refl
_ : compile-eval "[]"                ≡ inj₂ type-error -- type cannot be deduced
_ = refl
_ : compile-eval "([]) : ℕ"          ≡ inj₂ type-error -- Nat is not a List type
_ = refl
_ : compile-eval "([]) : [ℕ]" ≡ inj₁ (Ty.List Nat , nil , λ _ → [])
_ = refl

-- Trees
_ : compile-eval "<0> | (<1> | <2>)" ≡ inj₁ (Ty.Tree Nat , I.node (I.leaf zeroo)
                                                                  (I.node (I.leaf (suco zeroo))
                                                                          (I.leaf (suco (suco zeroo))))
                                                         , λ γ* → Tree.node (Tree.leaf 0)
                                                                            (Tree.node (Tree.leaf 1)
                                                                                       (Tree.leaf 2)))
_ = refl
_ : compile-eval "<0 , 0> | <0 , 1>" ≡ inj₁ (Ty.Tree (Nat ×o Nat) , I.node (I.leaf ⟨ zeroo ,      zeroo ⟩)
                                                                           (I.leaf ⟨ zeroo , suco zeroo ⟩)
                                                                  , λ γ* → Tree.node (Tree.leaf (0 , 0))
                                                                                     (Tree.leaf (0 , 1)))
_ = refl
_ : compile-eval "<0> | (<1> | <true>)" ≡ inj₂ type-error  -- different type of elements
_ = refl

-- Streams
evens = "genStream ((λn.n):ℕ→ℕ) ((λn.n+2):ℕ→ℕ) 0"
_ : compile-eval evens ≡ inj₁ (Ty.Stream Nat , I.genStream
                                               (lam q [ p ] $ q)
                                               (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                                                 $ q $ suco (suco zeroo)) [ p ] $ q)
                                               zeroo
                                             , λ γ* → STLC.genStream (λ x → x) (λ x → iteℕ 2 (λ y → suc y) x) 0)
_ = refl
_ : eval ("head "           ++ evens) ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval ("head tail "      ++ evens) ≡ inj₁ (Nat , λ γ* → 2)
_ = refl
_ : eval ("head tail tail " ++ evens) ≡ inj₁ (Nat , λ γ* → 4)
_ = refl

-- Machines
machine-code = "genMachine ((λx i. x+i) : ℕ→ℕ→ℕ) \
\                          ((λ_. 0)     : ℕ→ℕ)   \
\                          ((λx. x)     : ℕ→ℕ)   \
\                          0"
_ : compile-eval machine-code ≡ inj₁ (Ty.Machine , I.genMachine
                                     ((lam (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                                       $ q [ p ] $ q)) [ p ] $ q) [ p ] $ q) -- put:  add parameter to sum
                                     (lam zeroo [ p ] $ q)                   -- set:  reset sum to 0
                                     (lam q [ p ] $ q)                       -- get:  output current sum
                                     zeroo                                   -- seed: start sum from 0
                                   , λ γ* → STLC.genMachine (λ x y → iteℕ y (λ z → suc z) x) (λ x → 0) (λ x → x) 0)
_ = refl
_ : eval ("get " ++ machine-code)                                ≡ inj₁ (Nat , λ γ* →  0)
_ = refl
_ : eval ("get put " ++ machine-code ++ " 10")                   ≡ inj₁ (Nat , λ γ* → 10)
_ = refl
_ : eval ("get put put put " ++ machine-code ++ " 10 20 30")     ≡ inj₁ (Nat , λ γ* → 60)
_ = refl
_ : eval ("get put put set put " ++ machine-code ++ " 10 20 30") ≡ inj₁ (Nat , λ γ* → 50)
_ = refl

--------------------------------------
-- Some well-known functions

id-ℕ   = "(λ x . x)     : ℕ → ℕ"
+1     = "(λ x . x+1)   : ℕ → ℕ"
double = "(λ x . x+x)   : ℕ → ℕ"
triple = "(λ x . x+x+x) : ℕ → ℕ"
plus   = "(λ x y. iteℕ x ((λx.x + 1) : ℕ → ℕ) y) : ℕ → ℕ → ℕ"

_ : compile-eval id-ℕ ≡ inj₁ (Nat ⇒ Nat , lam q
                                        , λ γ* x → x)
_ = refl
_ : compile-eval +1 ≡ inj₁ (Nat ⇒ Nat , lam (lam (lam (iteNat q (suco q) (q [ p ]))) $ q $ suco zeroo)
                                      , λ γ* x → iteℕ 1 (λ y → suc y) x)
_ = refl
_ : compile-eval double ≡ inj₁ (Nat ⇒ Nat , lam (lam (lam (iteNat q (suco q) (q [ p ]))) $ q $ q)
                                          , λ γ* x → iteℕ x (λ y → suc y) x)
_ = refl
_ : compile-eval triple ≡ inj₁ (Nat ⇒ Nat , lam (lam (lam (iteNat q (suco q) (q [ p ])))
                                            $ (lam (lam (iteNat q (suco q) (q [ p ]))) $ q $ q) $ q)
                                          , λ γ* x → iteℕ x (λ y → suc y) (iteℕ x (λ y → suc y) x))
_ = refl
_ : compile-eval plus ≡ inj₁ (Nat ⇒ Nat ⇒ Nat , lam (lam (iteNat (q [ p ]) (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                                                $ q $ suco zeroo) [ p ] $ q) q))
                                              , λ γ* x y → iteℕ x (λ z → iteℕ 1 (λ w → suc w) z) y)
_ = refl

id-𝕃   = "(λ a  . a)                         : 𝕃 → 𝕃"
not    = "(λ a  . if a then false else true) : 𝕃 → 𝕃"
and    = "(λ a b. if a then b    else false) : 𝕃 → 𝕃 → 𝕃"
or     = "(λ a b. if a then true else b)     : 𝕃 → 𝕃 → 𝕃"
xor    = "(λ a b.          \
\          if a then        \
\            if b then      \
\              false        \
\            else           \
\              true         \
\          else if b then   \
\            true           \
\          else             \
\            false)         : 𝕃 → 𝕃 → 𝕃"

_ : compile-eval id-𝕃 ≡ inj₁ (Bool ⇒ Bool , lam q
                                          , λ γ* a → a)
_ = refl
_ : compile-eval not ≡ inj₁ (Bool ⇒ Bool , lam (iteBool false true q)
                                         , λ γ* a → if a then ff else tt)
_ = refl
_ : compile-eval and ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool q false (q [ p ])))
                                                , λ γ* a b → if a then b else ff)
_ = refl
_ : compile-eval or ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool true q (q [ p ])))
                                               , λ γ* a b → if a then tt else b)
_ = refl
_ : compile-eval xor ≡ inj₁ (Bool ⇒ Bool ⇒ Bool , lam (lam (iteBool (iteBool false true q) (iteBool true false q) (q [ p ])))
                                                , λ γ* a b → if a then if b then ff else tt else (if b then tt else ff))
_ = refl

twice   = "(λ f x  .   f f x) : (ℕ → ℕ) → ℕ → ℕ"
3-times = "(λ f x  . f f f x) : (ℕ → ℕ) → ℕ → ℕ"
_∘ℕ→ℕ_  = "(λ f g x.   f g x) : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ"

_ : compile-eval twice ≡ inj₁ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (q [ p ] $ (q [ p ] $ q)))
                                                       , λ γ* f x → f (f x))
_ = refl
_ : compile-eval 3-times ≡ inj₁ ((Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (q [ p ] $ (q [ p ] $ (q [ p ] $ q))))
                                                         , λ γ* f x → f (f (f x)))
_ = refl
_ : compile-eval _∘ℕ→ℕ_ ≡ inj₁ ((Nat ⇒ Nat) ⇒ (Nat ⇒ Nat) ⇒ Nat ⇒ Nat , lam (lam (lam (q [ p ] [ p ] $ (q [ p ] $ q))))
                                                                      , λ γ* f g x → f (g x))
_ = refl

isnil-[ℕ] = "(λ xs. iteList true ((λ _ _.false) : ℕ → 𝕃 → 𝕃) xs) : [ℕ] → 𝕃"
isnil-[𝕃] = "(λ xs. iteList true ((λ _ _.false) : 𝕃 → 𝕃 → 𝕃) xs) : [𝕃] → 𝕃"

sum-list = "(λ xs. iteList 0 ((λ x y. x + y) : ℕ → ℕ → ℕ) xs) : [ℕ] → ℕ"
sum-tree = "(λ t.  iteTree ((λ x.x) : ℕ → ℕ) ((λ l r. l + r) : ℕ → ℕ → ℕ) t) : (Tree ℕ) → ℕ"

concat = "(λ xs ys . iteList ys ((λ a as. a ∷ as) : ℕ → [ℕ] → [ℕ]) xs) : [ℕ] → [ℕ] → [ℕ]"

_ : compile-eval isnil-[ℕ] ≡ inj₁ (Ty.List Nat ⇒ Bool , lam (I.iteList true ((lam (lam false) [ p ] $ q) [ p ] $ q) q)
                                                      , λ γ* xs → STLC.iteList tt (λ _ _ → ff) xs)
_ = refl
_ : compile-eval isnil-[𝕃] ≡ inj₁ (Ty.List Bool ⇒ Bool , lam (I.iteList true ((lam (lam false) [ p ] $ q) [ p ] $ q) q)
                                                       , λ γ* xs → STLC.iteList tt (λ _ _ → ff) xs)
_ = refl

_ : compile-eval sum-list ≡ inj₁ (Ty.List Nat ⇒ Nat , lam (I.iteList zeroo ((lam (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                                                      $ q [ p ] $ q)) [ p ] $ q) [ p ] $ q) q)
                                                    , λ γ* xs → STLC.iteList 0 (λ x y → iteℕ y (λ z → suc z) x) xs)
_ = refl

_ : compile-eval sum-tree ≡ inj₁ (Ty.Tree Nat ⇒ Nat , lam (I.iteTree (lam q [ p ] $ q) ((lam (lam (lam (lam
                                                      (iteNat q (suco q) (q [ p ]))) $ q [ p ] $ q)) [ p ] $ q) [ p ] $ q) q)
                                                    , λ γ* t → STLC.iteTree (λ x → x) (λ x y → iteℕ y (λ z → suc z) x) t)
_ = refl

_ : compile-eval concat ≡ inj₁ (Ty.List Nat ⇒ Ty.List Nat ⇒ Ty.List Nat , lam (lam (I.iteList q ((lam (lam (cons (q [ p ]) q))
                                                                          [ p ] $ q) [ p ] $ q) (q [ p ])))
                                                                 , (λ γ* xs ys → STLC.iteList ys (λ a as → a ∷ as) xs))
_ = refl

-- Alpha equivalence

_ : compile-eval "(λx.x) : ℕ → ℕ" ≡ compile-eval "(λy.y) : ℕ → ℕ"
_ = refl

--------------------------------------
-- Some concrete computations

infixl 15 _++ₛ_
_++ₛ_ : String → String → String  -- safe source code concatenation with parentheses to preserve
s ++ₛ s' = parens s ++ parens s'  -- bounds of abstractions (i.e., λ extends as far right as possible)

_ : eval (triple ++ₛ "8") ≡ inj₁ (Nat , λ γ* → 24)
_ = refl
_ : eval (plus ++ₛ "3" ++ₛ "8") ≡ inj₁ (Nat , λ γ* → 11)
_ = refl
_ : eval (xor ++ₛ "true" ++ₛ "true") ≡ inj₁ (Bool , λ γ* → ff)
_ = refl
_ : eval (xor ++ₛ "true" ++ₛ "false") ≡ inj₁ (Bool , λ γ* → tt)
_ = refl
_ : eval (3-times ++ₛ +1 ++ₛ "10") ≡ inj₁ (Nat , λ γ* → 13)
_ = refl
_ : eval (_∘ℕ→ℕ_ ++ₛ double ++ₛ triple ++ₛ "10") ≡ inj₁ (Nat , λ γ* → 60)
_ = refl
_ : eval (sum-list ++ₛ "[]") ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval (sum-list ++ₛ "[10, 7, 20, 1]") ≡ inj₁ (Nat , λ γ* → 38)
_ = refl
_ : eval (sum-tree ++ₛ "<4>") ≡ inj₁ (Nat , λ γ* → 4)
_ = refl
_ : eval (sum-tree ++ₛ "<4> | ((<10> | <2>) | <3>)") ≡ inj₁ (Nat , λ γ* → 19)
_ = refl
_ : eval (concat ++ₛ "[]" ++ₛ "[]") ≡ inj₁ (Ty.List Nat , λ γ* → [])
_ = refl
_ : eval (concat ++ₛ "[10, 3]" ++ₛ "[5, 11, 7]") ≡ inj₁ (Ty.List Nat , λ γ* → 10 ∷ (3 ∷ (5 ∷ (11 ∷ (7 ∷ [])))))
_ = refl
