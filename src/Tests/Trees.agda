{-# OPTIONS --prop --rewriting --guardedness #-}

module Trees where

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

-- constructor <_> (leaf)

_ : compile-eval "<2>" ≡ inj₁ (Ty.Tree Nat , I.leaf (suco (suco zeroo)) , λ γ* → Tree.leaf 2)
_ = refl

_ : compile-eval "<true>" ≡ inj₁ (Ty.Tree Bool , I.leaf true , λ γ* → Tree.leaf tt)
_ = refl

-- constructor _|_ (binary branching)

{-    .
     / \.
    1  / \
      0   2
-}
_ : compile-eval "<1> | (<0> | <2>)" ≡ inj₁ (Ty.Tree Nat
                                       , I.node (I.leaf (suco zeroo)) (I.node (I.leaf zeroo) (I.leaf (suco (suco zeroo))))
                                       , λ γ* → Tree.node (Tree.leaf 1) (Tree.node (Tree.leaf 0) (Tree.leaf 2)))
_ = refl

{-      .
      ./ \
     / \  2
    1   0
-}
_ : compile-eval "(<1> | <0>) | <2>" ≡ inj₁ (Ty.Tree Nat
                                     , I.node (I.node (I.leaf (suco zeroo)) (I.leaf zeroo)) (I.leaf (suco (suco zeroo)))
                                     , λ γ* → Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 0)) (Tree.leaf 2))
_ = refl

-- tree of pairs
{-       .
        / \
    (F,T) (F,F)
-}
_ : compile-eval "<false,true> | <false,false>" ≡ inj₁ (Ty.Tree (Bool ×o Bool)
                                                     , I.node (I.leaf ⟨ false , true ⟩) (I.leaf ⟨ false , false ⟩)
                                                     , λ γ* → Tree.node (Tree.leaf (ff , tt)) (Tree.leaf (ff , ff)))
_ = refl

-- tree of lists
{-       .
        / \.
   [2,0]  / \
        [1]  [0,1]
-}
_ : compile-eval "<[2,0]> | (<[1]> | <[0,0,1]>)" ≡ inj₁ (Ty.Tree (Ty.List Nat)
                                               , I.node (I.leaf (cons (suco (suco zeroo)) (cons zeroo nil)))
                                                        (I.node (I.leaf (cons (suco zeroo) nil))
                                                                (I.leaf (cons zeroo (cons zeroo (cons (suco zeroo) nil)))))
                                               , λ γ* → Tree.node (Tree.leaf (2 ∷ (0 ∷ [])))
                                                                  (Tree.node (Tree.leaf (1 ∷ []))
                                                                             (Tree.leaf (0 ∷ (0 ∷ (1 ∷ []))))))
_ = refl

-- some well-known functions using the iterator (fold) of trees

-- count number of leaves

size = "(λ t. iteTree ((λ_. 1):ℕ→ℕ) (λ l r. l + r) t) : (Tree ℕ) → ℕ"

_ : compile-eval size ≡ inj₁ (Ty.Tree Nat ⇒ Nat
                           , lam (I.iteTree (lam (suco zeroo) [ p ] $ q) ((lam (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                             $ q [ p ] $ q)) [ p ] $ q) [ p ] $ q) q)
                           , λ γ* t → STLC.iteTree (λ _ → 1) (λ l r → iteℕ r (λ x → suc x) l) t)
_ = refl

_ : eval (size ++ₛ "<3>")                        ≡ inj₁ (Nat , λ γ* → 1)
_ = refl
_ : eval (size ++ₛ "<3> | ((<10> | <2>) | <3>)") ≡ inj₁ (Nat , λ γ* → 4)
_ = refl

-- sum leaves

sum = "(λ t. iteTree ((λx. x):ℕ→ℕ) (λ l r. l + r) t) : (Tree ℕ) → ℕ"

_ : compile-eval sum ≡ inj₁ (Ty.Tree Nat ⇒ Nat
                          , lam (I.iteTree (lam q [ p ] $ q) ((lam (lam (lam (lam (iteNat q (suco q) (q [ p ])))
                            $ q [ p ] $ q)) [ p ] $ q) [ p ] $ q) q)
                          , λ γ* t → STLC.iteTree (λ x → x) (λ l r → iteℕ r (λ x → suc x) l) t)
_ = refl

_ : eval (sum  ++ₛ "<3>")                        ≡ inj₁ (Nat , λ γ* → 3)
_ = refl
_ : eval (sum  ++ₛ "<3> | ((<10> | <2>) | <3>)") ≡ inj₁ (Nat , λ γ* → 18)
_ = refl

-- mapping

not  = "((λ a. if a then false else true) : 𝕃 → 𝕃)" 

even = "((λ x. iteℕ true (λa." ++ not ++ "a) x) : ℕ → 𝕃)" -- explained in Nats.agda

map = "(λ f t. iteTree ((λx.<f x>):ℕ→(Tree 𝕃)) (λ l r. l | r) t) : (ℕ → 𝕃) → (Tree ℕ) → (Tree 𝕃)"

_ : compile-eval map ≡ inj₁ ((Nat ⇒ Bool) ⇒ Ty.Tree Nat ⇒ Ty.Tree Bool
                          , lam (lam (I.iteTree (lam (I.leaf (q [ p ] [ p ] $ q)) [ p ] $ q)
                            ((lam (lam (I.node (q [ p ]) q)) [ p ] $ q) [ p ] $ q) q))
                          , λ γ* f t → STLC.iteTree (λ x → Tree.leaf (f x)) (λ l r → Tree.node l r) t)
_ = refl

_ : eval (map ++ₛ even ++ₛ "(<0> | <7>) | (<1> | <10>)") ≡ inj₁ (Ty.Tree Bool
                                                       , λ γ* → Tree.node (Tree.node (Tree.leaf tt) (Tree.leaf ff))
                                                                          (Tree.node (Tree.leaf ff) (Tree.leaf tt)))
_ = refl
