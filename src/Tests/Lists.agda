{-# OPTIONS --prop --rewriting --guardedness #-}

module Lists where

open import Data.Bool hiding (not) renaming (Bool to 𝟚; true to tt; false to ff)
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (_++_)
open import Data.Product using (_,_)
open import Data.Unit renaming (tt to triv)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Elaborator
open import STLC
open STLC.I

-- constructors: nil and ∷ (often called cons)

-- type of list cannot be infered in this case, so it must be annotated
_ : compile-eval "nil : List ℕ" ≡ inj₁ (Ty.List Nat , nil , λ _ → [])
_ = refl

-- shorter notation for list types:
_ : compile-eval "nil : [ℕ]" ≡ inj₁ (Ty.List Nat , nil , λ _ → [])
_ = refl

-- now type can be infered from the head of the list
_ : compile-eval "2 ∷ nil" ≡ inj₁ (Ty.List Nat , cons (suco (suco zeroo)) nil , λ γ* → 2 ∷ [])
_ = refl
_ : compile-eval "true ∷ nil" ≡ inj₁ (Ty.List Bool , cons true nil , λ γ* → tt ∷ [])
_ = refl

-- we can chain _∷_ (it's right associative)
_ : compile-eval "2 ∷ 1 ∷ 0 ∷ nil" ≡ inj₁ (Ty.List Nat , cons (suco (suco zeroo)) (cons (suco zeroo) (cons zeroo nil))
                                                       , λ γ* → 2 ∷ (1 ∷ (0 ∷ [])))
_ = refl
_ : compile-eval "true ∷ false ∷ nil" ≡ inj₁ (Ty.List Bool , cons true (cons false nil)
                                           , λ γ* → tt ∷ (ff ∷ []))
_ = refl

-- list of lists
_ : compile-eval "(0 ∷ 2 ∷ nil) ∷ (1 ∷ nil) ∷ nil" ≡ inj₁ (Ty.List (Ty.List Nat)
                                , cons (cons zeroo (cons (suco (suco zeroo)) nil)) (cons (cons (suco zeroo) nil) nil)
                                , λ γ* → (0 ∷ (2 ∷ [])) ∷ ((1 ∷ []) ∷ []))
_ = refl

-- list of pairs
_ : compile-eval "(0,true) ∷ (1,false) ∷ (2,true) ∷ nil" ≡ inj₁ (Ty.List (Nat ×o Bool)
                                                              ,  cons ⟨            zeroo  , true ⟩
                                                                (cons ⟨       suco zeroo  , false ⟩
                                                                (cons ⟨ suco (suco zeroo) , true ⟩ nil))
                                                              , (λ γ* → (0 , tt) ∷ ((1 , ff) ∷ ((2 , tt) ∷ []))))
_ = refl

-- list of trees
_ : compile-eval "(<1> | (<2> | <0>)) ∷ (<3> | <0>) ∷ nil" ≡ inj₁ (Ty.List (Ty.Tree Nat)
                                                                , cons (I.node (I.leaf (suco zeroo))
                                                                               (I.node (I.leaf (suco (suco zeroo)))
                                                                                       (I.leaf zeroo)))
                                                                 (cons (I.node (I.leaf (suco (suco (suco zeroo))))
                                                                               (I.leaf zeroo))
                                                                  nil)
                                                                , λ γ* → Tree.node (Tree.leaf 1)
                                                                                   (Tree.node (Tree.leaf 2)
                                                                                              (Tree.leaf 0))
                                                                      ∷ (Tree.node (Tree.leaf 3)
                                                                                   (Tree.leaf 0)
                                                                      ∷ []))
_ = refl

-- using the alternative (Haskell-like) syntax, we get the same terms

_ : compile-eval "([]) : [ℕ]"    ≡ compile-eval "nil : [ℕ]"
_ = refl
_ : compile-eval "[2]"           ≡ compile-eval "2 ∷ nil"
_ = refl
_ : compile-eval "[true]"        ≡ compile-eval "true ∷ nil"
_ = refl
_ : compile-eval "[2, 1, 0]"     ≡ compile-eval "2 ∷ 1 ∷ 0 ∷ nil"
_ = refl
_ : compile-eval "[true, false]" ≡ compile-eval "true ∷ false ∷ nil"
_ = refl
_ : compile-eval "(0,true) ∷ (1,false) ∷ (2,true) ∷ nil" ≡ compile-eval "[(0,true),(1,false),(2,true)]"
_ = refl

-- note: nested lists using this alternative syntax do not work yet

-- some well-known functions using the iterator of lists
--   note: some of these would make sense with any [A], but we cannot write polymorphic functions, so we'll stick with [ℕ]

-- empty check

isnil = "(λ xs. iteList true (λ _ _.false) xs) : [ℕ] → 𝕃"

_ : compile-eval isnil ≡ inj₁ (Ty.List Nat ⇒ Bool , lam (I.iteList true ((lam (lam false) [ p ] $ q) [ p ] $ q) q)
                                                  , λ γ* xs → STLC.iteList tt (λ _ _ → ff) xs)
_ = refl

_ : eval (isnil ++ₛ "[]") ≡ inj₁ (Bool , λ γ* → tt)
_ = refl
_ : eval (isnil ++ₛ "[0]") ≡ inj₁ (Bool , λ γ* → ff)
_ = refl

-- length

length = "(λ xs. iteList 0 (λ _ x. x+1) xs) : [ℕ] → ℕ"

_ : compile-eval length ≡ inj₁ (Ty.List Nat ⇒ Nat , lam (I.iteList zeroo ((lam (lam (iteNat (suco zeroo) (suco q) q))
                                                    [ p ] $ q) [ p ] $ q) q)
                                                  , λ γ* xs → STLC.iteList 0 (λ x y → iteℕ 1 (λ z → suc z) y) xs)
_ = refl

_ : eval (length ++ₛ "[]") ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval (length ++ₛ "[1,2,3,4,5]") ≡ inj₁ (Nat , λ γ* → 5)
_ = refl

-- folding (iteList could be called foldl)

sum = "(λ xs. iteList 0 (λ x y. x + y) xs) : [ℕ] → ℕ"

_ : compile-eval sum ≡ inj₁ (Ty.List Nat ⇒ Nat , lam (I.iteList zeroo ((lam (lam (iteNat q (suco q) (q [ p ])))
                                                 [ p ] $ q) [ p ] $ q) q)
                                               , λ γ* xs → STLC.iteList 0 (λ x y → iteℕ y (λ z → suc z) x) xs)
_ = refl

_ : eval (sum ++ₛ "[]") ≡ inj₁ (Nat , λ γ* → 0)
_ = refl
_ : eval (sum ++ₛ "[10, 7, 20, 1]") ≡ inj₁ (Nat , λ γ* → 38)
_ = refl

-- concatenation

concat = "(λ xs ys. iteList ys (λ a as. a ∷ as) xs) : [ℕ] → [ℕ] → [ℕ]"

_ : compile-eval concat ≡ inj₁ (Ty.List Nat ⇒ Ty.List Nat ⇒ Ty.List Nat
                               , lam (lam (I.iteList q ((lam (lam (cons (q [ p ]) q)) [ p ] $ q) [ p ] $ q) (q [ p ])))
                               , λ γ* xs ys → STLC.iteList ys (λ a as → a ∷ as) xs)
_ = refl

_ : eval (concat ++ₛ "[]" ++ₛ "[]") ≡ inj₁ (Ty.List Nat , λ γ* → [])
_ = refl
_ : eval (concat ++ₛ "[3,1]" ++ₛ "[4,1,5]") ≡ inj₁ (Ty.List Nat , λ γ* → 3 ∷ (1 ∷ (4 ∷ (1 ∷ (5 ∷ [])))))
_ = refl

-- total implementation of head, which returns an error on empty lists (we simulate Maybe with ⊤ ⊎ ℕ)

headM = "(λ xs. iteList ((inl trivial) : ⊤ ⊎ ℕ) (λ a as. ((inr a) : ⊤ ⊎ ℕ)) xs) : [ℕ] → ⊤ ⊎ ℕ"

_ : compile-eval headM ≡ inj₁ (Ty.List Nat ⇒ (Unit +o Nat)
                            , lam (I.iteList (inl trivial) ((lam (lam (inr (q [ p ]))) [ p ] $ q) [ p ] $ q) q)
                            , λ γ* xs → STLC.iteList (inj₁ triv) (λ a as → inj₂ a) xs)
_ = refl

_ : eval (headM ++ₛ "[]") ≡ inj₁ (Unit +o Nat , λ γ* → inj₁ triv)
_ = refl
_ : eval (headM ++ₛ "[2,4,6]") ≡ inj₁ (Unit +o Nat , λ γ* → inj₂ 2)
_ = refl

-- filtering

not  = "((λ a. if a then false else true) : 𝕃 → 𝕃)" 

even = "((λ x. iteℕ true (λa." ++ not ++ "a) x) : ℕ → 𝕃)" -- explained in Nats.agda

filter = "(λ f xs. iteList (nil : [ℕ]) (λ a as. if (f a) then a ∷ as else as) xs) : (ℕ → 𝕃) → [ℕ] → [ℕ]"

_ : compile-eval filter ≡ inj₁ ((Nat ⇒ Bool) ⇒ Ty.List Nat ⇒ Ty.List Nat ,
                               lam (lam (I.iteList nil ((lam (lam (iteBool (cons (q [ p ]) q) q
                               (q [ p ] [ p ] [ p ] $ q [ p ]))) [ p ] $ q) [ p ] $ q) q))
                             , λ γ* f xs → STLC.iteList [] (λ a as → if f a then a ∷ as else as) xs)
_ = refl

_ : eval (filter ++ₛ even ++ₛ "[]") ≡ inj₁ (Ty.List Nat , λ γ* → [])
_ = refl
_ : eval (filter ++ₛ even ++ₛ "[1,2,3,4,5,6,7,8]") ≡ inj₁ (Ty.List Nat , λ γ* → 2 ∷ (4 ∷ (6 ∷ (8 ∷ []))))
_ = refl

-- mapping

double = "(λ x. x+x) : ℕ → ℕ"

map = "(λ f xs. iteList (nil : [ℕ]) (λ a as. (f a) ∷ as) xs) : (ℕ → ℕ) → [ℕ] → [ℕ]"

_ : compile-eval map ≡ inj₁ ((Nat ⇒ Nat) ⇒ Ty.List Nat ⇒ Ty.List Nat
                          , lam (lam (I.iteList nil ((lam (lam (cons (q [ p ] [ p ] [ p ] $ q [ p ]) q))
                            [ p ] $ q) [ p ] $ q) q))
                          , λ γ* f xs → STLC.iteList [] (λ a as → f a ∷ as) xs)
_ = refl

_ : eval (map ++ₛ double ++ₛ "[3,0,11,23]") ≡ inj₁ (Ty.List Nat , λ γ* → 6 ∷ (0 ∷ (22 ∷ (46 ∷ []))))
_ = refl
_ : eval (map ++ₛ double ++ₛ "[]") ≡ inj₁ (Ty.List Nat , λ γ* → [])
_ = refl

-- replicating

replicate = "(λ n x. iteℕ (nil : [ℕ]) (λ xs. x ∷ xs) n) : ℕ → ℕ → [ℕ]"

_ : compile-eval replicate ≡ inj₁ (Nat ⇒ Nat ⇒ Ty.List Nat
                                , lam (lam (iteNat nil (lam (cons (q [ p ]) q) [ p ] $ q) (q [ p ])))
                                , λ γ* n x → iteℕ [] (λ xs → x ∷ xs) n)
_ = refl

_ : eval (replicate ++ₛ "4" ++ₛ "42") ≡ inj₁ (Ty.List Nat , λ γ* → 42 ∷ (42 ∷ (42 ∷ (42 ∷ []))))
_ = refl
_ : eval (replicate ++ₛ "0" ++ₛ "42") ≡ inj₁ (Ty.List Nat , λ γ* → [])
_ = refl
