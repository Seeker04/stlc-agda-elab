module Scopecheck where

open import Agda.Builtin.Sigma using (Σ)
open import Level hiding (suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Nat using (ℕ; suc; pred)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; _∷_; []; [_]; concat)
open import Data.String using (String; _==_)
open import Data.Product using (_×_; _,_) renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (case_of_)

open import Lexer
open import Parser Level.zero

--------------------------------------
-- Abstract Binding Tree

infixl 15 _abt-+_
infixl 15 _abt-$_
infixr 15 _abt-,_
infixr 15 _abt-∷_
infixr 15 _abt-node_

data ABT (n : ℕ) : Set where  -- indexed by number of free variables, i.e., size of context it needs
  abt-true       : ABT n
  abt-false      : ABT n
  abt-ite        : ABT n → ABT n → ABT n → ABT n
  abt-isZero     : ABT n → ABT n
  _abt-+_        : ABT n → ABT n → ABT n
  abt-num        : ℕ → ABT n
  abt-λ          : ABT (suc n) → ABT n   -- λ x y z... is unrolled to λ (λ (λ ...))
  _abt-$_        : ABT n → ABT n → ABT n
  abt-var        : Fin n → ABT n         -- now we use De Bruijn indices instead of variable names

  abt-triv       : ABT n
  _abt-,_        : ABT n → ABT n → ABT n
  abt-fst        : ABT n → ABT n
  abt-snd        : ABT n → ABT n

  abt-inl        : ABT n → ABT n
  abt-inr        : ABT n → ABT n
  abt-case       : ABT n → ABT n → ABT n

  abt-nil        : ABT n
  _abt-∷_        : ABT n → ABT n → ABT n

  abt-leaf       : ABT n → ABT n
  _abt-node_     : ABT n → ABT n → ABT n

  abt-iteℕ       : ABT n → ABT n → ABT n → ABT n
  abt-iteList    : ABT n → ABT n → ABT n → ABT n
  abt-iteTree    : ABT n → ABT n → ABT n → ABT n

  abt-head       : ABT n → ABT n
  abt-tail       : ABT n → ABT n
  abt-genStream  : ABT n → ABT n → ABT n → ABT n

  abt-put        : ABT n → ABT n → ABT n
  abt-set        : ABT n → ABT n
  abt-get        : ABT n → ABT n
  abt-genMachine : ABT n → ABT n → ABT n → ABT n → ABT n

  abt-ann        : ABT n → SType → ABT n

_≤_ : ℕ → ℕ → Set
0     ≤ _     = ⊤
suc n ≤ 0     = ⊥
suc n ≤ suc m = n ≤ m

lift-abt : {m n : ℕ} → (m ≤ n) → ABT m → ABT n  -- we can always embed into bigger context
lift-abt m≤n abt-true            = abt-true
lift-abt m≤n abt-false           = abt-false
lift-abt m≤n (abt-ite t u v)     = abt-ite (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-isZero t)      = abt-isZero (lift-abt m≤n t)
lift-abt m≤n (u abt-+ v)         = (lift-abt m≤n u) abt-+ (lift-abt m≤n v)
lift-abt m≤n (abt-num n)         = abt-num n
lift-abt m≤n (abt-λ t)           = abt-λ (lift-abt m≤n t)
lift-abt m≤n (u abt-$ v)         = (lift-abt m≤n u) abt-$ (lift-abt m≤n v)
lift-abt {m} {n} m≤n (abt-var f) = abt-var (inject≤ {m} {n} f m≤n) where
  inject≤ : {m n : ℕ} → Fin m → m ≤ n → Fin n
  inject≤ {_} {suc n} zero    _     = Fin.zero
  inject≤ {_} {suc n} (suc i) (m≤n) = suc (inject≤ i m≤n)
lift-abt m≤n abt-triv            = abt-triv
lift-abt m≤n (u abt-, v)         = (lift-abt m≤n u) abt-, (lift-abt m≤n v)
lift-abt m≤n (abt-fst t)         = abt-fst (lift-abt m≤n t)
lift-abt m≤n (abt-snd t)         = abt-snd (lift-abt m≤n t)
lift-abt m≤n (abt-inl t)         = abt-inl (lift-abt m≤n t)
lift-abt m≤n (abt-inr t)         = abt-inr (lift-abt m≤n t)
lift-abt m≤n (abt-case u v)      = abt-case (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n abt-nil             = abt-nil
lift-abt m≤n (abt-leaf t)        = abt-leaf (lift-abt m≤n t)
lift-abt m≤n (u abt-node v)      = (lift-abt m≤n u) abt-node (lift-abt m≤n v)
lift-abt m≤n (u abt-∷ v)         = (lift-abt m≤n u) abt-∷ (lift-abt m≤n v)
lift-abt m≤n (abt-iteℕ    t u v) = abt-iteℕ    (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-iteList t u v) = abt-iteList (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-iteTree t u v) = abt-iteTree (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-head t)        = abt-head (lift-abt m≤n t)
lift-abt m≤n (abt-tail t)        = abt-tail (lift-abt m≤n t)
lift-abt m≤n (abt-genStream t u v) = abt-genStream (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-put u v)       = abt-put (lift-abt m≤n u) (lift-abt m≤n v)
lift-abt m≤n (abt-set t)         = abt-set (lift-abt m≤n t)
lift-abt m≤n (abt-get t)         = abt-get (lift-abt m≤n t)
lift-abt m≤n (abt-genMachine t u v w) = abt-genMachine (lift-abt m≤n t) (lift-abt m≤n u) (lift-abt m≤n v) (lift-abt m≤n w)
lift-abt m≤n (abt-ann t ty)      = abt-ann (lift-abt m≤n t) ty

-- some helper lemmas
≡implies≤ : (n m : ℕ) → n ≡ m → n ≤ m
≡implies≤ 0 m eq = tt
≡implies≤ (suc n) (suc m) eq = ≡implies≤ n m (cong pred eq)

max : ℕ → ℕ → ℕ
max 0 n = n
max (suc n) 0 = suc n
max (suc n) (suc m) = suc (max n m)

≤-max2 : (n m : ℕ) → (n ≤ max n m) × (m ≤ max n m)
≤-max2 0       0       = tt                 , tt
≤-max2 0       (suc m) = tt                 , π₂ (≤-max2 0 m)
≤-max2 (suc n) 0       = ≡implies≤ n n refl , tt
≤-max2 (suc n) (suc m) = π₁ (≤-max2 n m)    , π₂ (≤-max2 n m)

≤-max3 : (n m k : ℕ) → (n ≤ max (max n m) k) × (m ≤ max (max n m) k) × (k ≤ max (max n m) k)
≤-max3 0       0       0       = tt                     , tt                     , tt
≤-max3 0       0       (suc k) = tt                     , tt                     , π₂ (π₂ (≤-max3 0 0 k))
≤-max3 0       (suc m) 0       = tt                     , ≡implies≤ m m refl     , tt
≤-max3 0       (suc m) (suc k) = tt                     , π₁ (π₂ (≤-max3 0 m k)) , π₂ (π₂ (≤-max3 0 m k))
≤-max3 (suc n) 0       k       = π₁ (≤-max2 (suc n) k)  , tt                     , π₂ (≤-max2 (suc n) k)
≤-max3 (suc n) (suc m) 0       = π₁ (π₂ (≤-max3 0 n m)) , π₂ (π₂ (≤-max3 0 n m)) , tt
≤-max3 (suc n) (suc m) (suc k) = π₁ (≤-max3 n m k)      , π₁ (π₂ (≤-max3 n m k)) , π₂ (π₂ (≤-max3 n m k))

≤-max4 : (n m k l : ℕ) → (n ≤ max (max (max n m) k) l) × (m ≤ max (max (max n m) k) l) ×
                         (k ≤ max (max (max n m) k) l) × (l ≤ max (max (max n m) k) l)
≤-max4 0       m       k       l       = tt , π₁ (≤-max3 m k l) , π₁ (π₂ (≤-max3 m k l)) , π₂ (π₂ (≤-max3 m k l))
≤-max4 (suc n) 0       k       l       = π₁ (≤-max3 (suc n) k l) , tt , π₁ (π₂ (≤-max3 (suc n) k l)) , π₂ (π₂ (≤-max3 (suc n) k l))
≤-max4 (suc n) (suc m) 0       0       = π₁ (≤-max2 n m) , π₂ (≤-max2 n m) , tt , tt
≤-max4 (suc n) (suc m) 0       (suc l) = π₁ (≤-max3 n m l) , π₁ (π₂ (≤-max3 n m l)) , tt , π₂ (π₂ (≤-max3 n m l))
≤-max4 (suc n) (suc m) (suc k) 0       = π₁ (≤-max3 n m k) , π₁ (π₂ (≤-max3 n m k)) , π₂ (π₂ (≤-max3 n m k)) , tt
≤-max4 (suc n) (suc m) (suc k) (suc l) = π₁ (≤-max4 n m k l) , π₁ (π₂ (≤-max4 n m k l)) ,
                                         π₁ (π₂ (π₂ (≤-max4 n m k l))) , π₂ (π₂ (π₂ (≤-max4 n m k l)))

--------------------------------------
-- Scope inference and check

lookup : List String → String → Maybe ℕ
lookup = step 0 where
  step : ℕ → List String → String → Maybe ℕ
  step n (s ∷ ss) str = if (s == str) then just n else step (suc n) ss str
  step _ []       _   = nothing

scopeinfer : AST → Maybe (Σ ℕ λ n → ABT n)
scopeinfer = sinfer [] where

  sinfer : List String → AST → Maybe (Σ ℕ λ n → ABT n)

  sinfer ss s-true  = just (0 , abt-true)
  sinfer ss s-false = just (0 , abt-false)

  sinfer ss (s-ite t u v) with sinfer ss t | sinfer ss u | sinfer ss v
  ... | just (i , t') | just (j , u') | just (k , v') = just (max (max i j) k ,
                                                             abt-ite (lift-abt (π₁     (≤-max3 i j k))  t')
                                                                     (lift-abt (π₁ (π₂ (≤-max3 i j k))) u')
                                                                     (lift-abt (π₂ (π₂ (≤-max3 i j k))) v'))
  -- whichever of the three subterms requires the biggest context is the size if_then_else_ will need
  ... | _ | _ | _ = nothing

  sinfer ss (s-isZero t) with sinfer ss t
  ... | just (i , t') = just (i , (abt-isZero t'))
  ... | nothing       = nothing

  sinfer ss (u s-+ v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , _abt-+_ (lift-abt (π₁ (≤-max2 i j)) u')
                                                                (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing

  sinfer ss (s-num n) = just (0 , abt-num n)

  sinfer ss (s-λ       [] t) = sinfer ss t
  sinfer ss (s-λ (v ∷ vs) t) with sinfer (v ∷ ss) (s-λ vs t)
  ... | just (0     , t') = just (0 , abt-λ (lift-abt tt t'))
  ... | just (suc n , t') = just (n , abt-λ t')
  ... | nothing = nothing

  sinfer ss (u s-$ v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , _abt-$_ (lift-abt (π₁ (≤-max2 i j)) u')
                                                                (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing

  sinfer ss (s-var name) = case (lookup ss name) of λ where
    nothing  → nothing -- not in scope
    (just i) → just (suc i , abt-var (fromℕ i)) where
      fromℕ : (n : ℕ) → Fin (suc n)
      fromℕ = λ { 0 → Fin.zero ; (suc n) → suc (fromℕ n) }

  sinfer ss s-triv = just (0 , abt-triv)

  sinfer ss (u s-, v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , _abt-,_ (lift-abt (π₁ (≤-max2 i j)) u')
                                                                (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing
                                          
  sinfer ss (s-fst t) with (sinfer ss t)
  ... | just (i , t') = just (i , abt-fst t')
  ... | _             = nothing
  sinfer ss (s-snd t) with (sinfer ss t)
  ... | just (i , t') = just (i , abt-snd t')
  ... | _             = nothing
  sinfer ss (s-inl t) with (sinfer ss t)
  ... | just (i , t') = just (i , abt-inl t')
  ... | _             = nothing
  sinfer ss (s-inr t) with (sinfer ss t)
  ... | just (i , t') = just (i , abt-inr t')
  ... | _             = nothing

  sinfer ss (s-case u v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , abt-case (lift-abt (π₁ (≤-max2 i j)) u')
                                                                 (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing

  sinfer ss s-nil = just (0 , abt-nil)
  sinfer ss (u s-∷ v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , _abt-∷_ (lift-abt (π₁ (≤-max2 i j)) u')
                                                                (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing

  sinfer ss (s-leaf t) with sinfer ss t
  ... | just (i , t') = just (i , abt-leaf t')
  ... | nothing       = nothing
  sinfer ss (u s-node v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , _abt-node_ (lift-abt (π₁ (≤-max2 i j)) u')
                                                                   (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing

  sinfer ss (s-iteℕ t u v) with sinfer ss t | sinfer ss u | sinfer ss v
  ... | just (i , t') | just (j , u') | just (k , v') = just (max (max i j) k ,
                                                             abt-iteℕ (lift-abt (π₁     (≤-max3 i j k))  t')
                                                                      (lift-abt (π₁ (π₂ (≤-max3 i j k))) u')
                                                                      (lift-abt (π₂ (π₂ (≤-max3 i j k))) v'))
  ... | _ | _ | _ = nothing

  sinfer ss (s-iteList t u v) with sinfer ss t | sinfer ss u | sinfer ss v
  ... | just (i , t') | just (j , u') | just (k , v') = just (max (max i j) k ,
                                                             abt-iteList (lift-abt (π₁     (≤-max3 i j k))  t')
                                                                         (lift-abt (π₁ (π₂ (≤-max3 i j k))) u')
                                                                         (lift-abt (π₂ (π₂ (≤-max3 i j k))) v'))
  ... | _ | _ | _ = nothing

  sinfer ss (s-iteTree t u v) with sinfer ss t | sinfer ss u | sinfer ss v
  ... | just (i , t') | just (j , u') | just (k , v') = just (max (max i j) k ,
                                                             abt-iteTree (lift-abt (π₁     (≤-max3 i j k))  t')
                                                                         (lift-abt (π₁ (π₂ (≤-max3 i j k))) u')
                                                                         (lift-abt (π₂ (π₂ (≤-max3 i j k))) v'))
  ... | _ | _ | _ = nothing

  sinfer ss (s-head t) with sinfer ss t
  ... | just (i , t') = just (i , abt-head t')
  ... | nothing       = nothing
  sinfer ss (s-tail t) with sinfer ss t
  ... | just (i , t') = just (i , abt-tail t')
  ... | nothing       = nothing
  sinfer ss (s-genStream t u v) with sinfer ss t | sinfer ss u | sinfer ss v
  ... | just (i , t') | just (j , u') | just (k , v') = just (max (max i j) k ,
                                                             abt-genStream (lift-abt (π₁     (≤-max3 i j k))  t')
                                                                           (lift-abt (π₁ (π₂ (≤-max3 i j k))) u')
                                                                           (lift-abt (π₂ (π₂ (≤-max3 i j k))) v'))
  ... | _ | _ | _ = nothing

  sinfer ss (s-put u v) with sinfer ss u | sinfer ss v
  ... | just (i , u') | just (j , v') = just (max i j , abt-put (lift-abt (π₁ (≤-max2 i j)) u')
                                                                (lift-abt (π₂ (≤-max2 i j)) v'))
  ... | _ | _ = nothing
  sinfer ss (s-set t) with sinfer ss t
  ... | just (i , t') = just (i , abt-set t')
  ... | nothing       = nothing
  sinfer ss (s-get t) with sinfer ss t
  ... | just (i , t') = just (i , abt-get t')
  ... | nothing       = nothing
  sinfer ss (s-genMachine t u v w) with sinfer ss t | sinfer ss u | sinfer ss v | sinfer ss w
  ... | just (i , t') | just (j , u') | just (k , v') | just (l , w') = just (max (max (max i j) k) l ,
                                                                        abt-genMachine
                                                                        (lift-abt (π₁         (≤-max4 i j k l))   t')
                                                                        (lift-abt (π₁ (π₂     (≤-max4 i j k l)))  u')
                                                                        (lift-abt (π₁ (π₂ (π₂ (≤-max4 i j k l)))) v')
                                                                        (lift-abt (π₂ (π₂ (π₂ (≤-max4 i j k l)))) w'))
  ... | _ | _ | _ | _ = nothing

  sinfer ss (s-ann t ty) with sinfer ss t
  ... | just (i , t') = just (i , abt-ann t' ty)
  ... | nothing       = nothing


scopecheck : AST → Maybe (ABT 0)   -- must be a closed term, i.e., with no free variables at the top level
scopecheck ast with scopeinfer ast
... | just (0 , abt) = just abt
... | _              = nothing

--------------------------------------
-- Examples (see: Tests.agda for more)

private
  _ : scopecheck (s-var "foo") ≡ nothing
  _ = refl
  _ : scopecheck (s-λ ("foo" ∷ []) (s-var "bar")) ≡ nothing
  _ = refl
  _ : scopecheck (s-λ ("foo" ∷ []) (s-var "foo")) ≡ just (abt-λ (abt-var Fin.zero))
  _ = refl
  _ : scopecheck (s-λ ("x" ∷ "y" ∷ []) (s-var "x" s-+ s-var "y")) ≡ just (abt-λ (abt-λ (
                                                                         abt-var (suc Fin.zero) abt-+ abt-var Fin.zero)))
  _ = refl
