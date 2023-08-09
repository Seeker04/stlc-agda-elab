open import Level using (Level)

module Parser (l : Level) where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.Maybe

open import Level.Bounded renaming (_×_ to _×b_; List to Listb) hiding (Maybe; Vec; List⁺)

import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Char.Base as Char using (Char)
import Data.Empty as Empty
open import Data.Product using (_×_; _,_; proj₁)

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Categorical as List
open import Data.List.Sized.Interface
open import Data.List.NonEmpty using (List⁺; _∷_; toList)

open import Data.String as String hiding (toList)
open import Data.Vec as Vec using ()
open import Data.Bool
open import Data.Maybe as Maybe using (nothing; just; maybe′)
open import Data.Maybe.Categorical as MaybeCat
open import Data.Sum
open import Function
open import Category.Monad
open import Category.Monad.State
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Relation.Unary using (IUniversal; _⇒_) public
open import Relation.Binary.PropositionalEquality.Decidable public
open import Induction.Nat.Strong hiding (<-lower ; ≤-lower) public

open import Data.Subset public
open import Data.Singleton public

open import Text.Parser.Types.Core                public
open import Text.Parser.Types                     public
open import Text.Parser.Position                  public
open import Text.Parser.Combinators               public
open import Text.Parser.Combinators.Char          public
open import Text.Parser.Combinators.Numbers       public
open import Text.Parser.Monad                     public
open import Text.Parser.Monad.Result hiding (map) public

open import Lexer
open import Text.Lexer keywords breaking default hiding (Result) renaming (tokenize to tokenize')

open Agdarsec′ public

-- TODO: lists if present as sub-expressions always have to be parenthesised, which shouldn't be necessary
-- TODO: nested lists are parsed incorrectly when using the alternative "[a,b,c]" list syntax

--------------------------------------
-- Boilerplate

record Tokenizer (A : Set≤ l) : Set (level (level≤ A)) where
  constructor mkTokenizer
  field tokenize : List.List Char → List.List (theSet A)

  fromText : String → List.List (theSet A)
  fromText = tokenize ∘ String.toList

instance
  tokChar : Tokenizer [ Char ]
  tokChar = mkTokenizer id

record RawMonadRun (M : Set l → Set l) : Set (Level.suc l) where
  field runM : ∀ {A} → M A → List.List A
open RawMonadRun public

instance

  Agdarsec′M : RawMonad (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M  = Agdarsec′.monad

  Agdarsec′M0 : RawMonadZero (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M0 = Agdarsec′.monadZero

  Agdarsec′M+ : RawMonadPlus (Agdarsec {l} ⊤ ⊥)
  Agdarsec′M+ = Agdarsec′.monadPlus

  runMaybe : RawMonadRun Maybe.Maybe
  runMaybe = record { runM = maybe′ (_∷ []) [] }

  runList : RawMonadRun List.List
  runList = record { runM = id }

  runResult : {E : Set l} → RawMonadRun (Result E)
  runResult = record { runM = result (const []) (const []) (_∷ []) }

  runStateT : ∀ {M A} {{𝕄 : RawMonadRun M}} → RawMonadRun (StateT (Lift ([ Position ] ×b Listb A)) M)
  runStateT {{𝕄}} .RawMonadRun.runM =
    List.map proj₁
    ∘′ runM 𝕄
    ∘′ (_$ lift (start , []))

  monadMaybe : RawMonad {l} Maybe.Maybe
  monadMaybe = MaybeCat.monad

  plusMaybe : RawMonadPlus {l} Maybe.Maybe
  plusMaybe = MaybeCat.monadPlus

  monadList : RawMonad {l} List.List
  monadList = List.monad

  plusList : RawMonadPlus {l} List.List
  plusList = List.monadPlus

instance
  _ : Tokenizer [ Position × Tok ]
  _ = record { tokenize = tokenize' ∘ fromList }

--------------------------------------
-- Abstract Syntax Tree

infixr 15 _s-→_
infixr 15 _s-×_
infixr 15 _s-⊎_

infixl 15 _s-+_
infixl 15 _s-$_
infixr 15 _s-,_
infixr 15 _s-∷_
infixl 15 _s-node_

data SType : Set where  -- syntax of type annotations
  s-Nat     : SType
  s-Bool    : SType
  _s-→_     : SType → SType → SType
  s-⊤       : SType
  s-⊥       : SType
  _s-×_     : SType → SType → SType
  _s-⊎_     : SType → SType → SType
  s-List    : SType → SType
  s-Tree    : SType → SType
  s-Stream  : SType → SType
  s-Machine : SType

data AST : Set where
  s-true       : AST
  s-false      : AST
  s-ite        : AST → AST → AST → AST
  s-isZero     : AST → AST
  _s-+_        : AST → AST → AST
  s-num        : ℕ → AST
  s-λ          : List String → AST → AST
  s-var        : String → AST
  _s-$_        : AST → AST → AST

  s-triv       : AST
  _s-,_        : AST → AST → AST
  s-fst        : AST → AST
  s-snd        : AST → AST

  s-inl        : AST → AST
  s-inr        : AST → AST
  s-case       : AST → AST → AST

  s-nil        : AST
  _s-∷_        : AST → AST → AST

  s-leaf       : AST → AST
  _s-node_     : AST → AST → AST

  s-iteℕ       : AST → AST → AST → AST
  s-iteList    : AST → AST → AST → AST
  s-iteTree    : AST → AST → AST → AST

  s-head       : AST → AST
  s-tail       : AST → AST
  s-genStream  : AST → AST → AST → AST

  s-put        : AST → AST → AST
  s-set        : AST → AST
  s-get        : AST → AST
  s-genMachine : AST → AST → AST → AST → AST

  s-ann        : AST → SType → AST

--------------------------------------
-- Building parsers with combinators

module ParserM = Agdarsec l [ Position ] ⊥ (record { into = proj₁ })

instance
  _ = ParserM.monadZero
  _ = ParserM.monadPlus
  _ = ParserM.monad

P = ParserM.param [ Token ] (λ n → [ Vec.Vec Token n ]) λ where (p , _) _ → Value (_ , lift (p , []))

p-tok : Tok → ∀[ Parser P [ Token ] ]
p-tok t = maybeTok $ λ where
  tok@(_ , t') → case eq-tok t t' of λ where
    (yes eq) → just tok
    (no ¬eq) → nothing

p-parens : ∀ {A} → ∀[ □ Parser P A ⇒ Parser P A ]
p-parens rec = p-tok t-lpar &> rec <& box (p-tok t-rpar)

p-name : ∀[ Parser P [ String ] ]
p-name = maybeTok λ where (_ , t-var s) → just s; _ → nothing

p-type : ∀[ Parser P [ SType ] ]
p-type = fix _ $ λ rec →
  let p-nat     = s-Nat     <$ p-tok t-ℕ
      p-bool    = s-Bool    <$ p-tok t-𝕃
      p-unit    = s-⊤       <$ p-tok t-⊤
      p-empty   = s-⊥       <$ p-tok t-⊥
      p-machine = s-Machine <$ p-tok t-Machine
      p-list'   = s-List    <$> (p-tok t-[ &> rec <& box (p-tok t-]))

      p-atom = p-nat <|> p-bool <|> p-unit <|> p-empty <|> p-machine <|> p-list' <|> p-parens rec
      p-×    = chainr1 p-atom (box (_s-×_ <$ p-tok t-×))
      p-+    = chainr1 p-×    (box (_s-⊎_ <$ p-tok t-⊎))
      p-→    = chainr1 p-+    (box (_s-→_ <$ p-tok t-→))
      -- note: this order of embedding determines the precedence between these operators
      --       the same is true below, e.g., between + and ,

      p-list   = s-List   <$> (p-tok t-List   &> box p-atom)
      p-tree   = s-Tree   <$> (p-tok t-Tree   &> box p-atom)
      p-stream = s-Stream <$> (p-tok t-Stream &> box p-atom)

  in p-→ <|> p-list <|> p-tree <|> p-stream

-- non-recursive nodes
p-true p-false p-num p-var p-triv p-nil : ∀[ Parser P [ AST ] ]

-- recursive nodes
p-ite p-isZero p-fst p-snd p-inl p-inr p-case p-λ p-$ p-+ p-,
 p-iteℕ p-iteList p-iteTree p-subexp p-∷ p-list p-leaf p-node
 p-head p-tail p-genStream p-put p-set p-get p-genMachine p-ann : ∀[ □ Parser P [ AST ] ⇒ Parser P [ AST ] ]

p-true  = s-true  <$ p-tok t-true
p-false = s-false <$ p-tok t-false
p-triv  = s-triv  <$ p-tok t-triv
p-nil   = s-nil   <$ p-tok t-nil

p-var = s-var <$> p-name

p-num = let p-ℕ : ∀[ Parser P [ ℕ ] ]
            p-ℕ = maybeTok λ where (_ , t-num n) → just n; _ → nothing
        in s-num <$> p-ℕ

p-ite rec = s-ite
            <$>     (p-tok t-if   &> rec)
            <*> box (p-tok t-then &> rec)
            <*> box (p-tok t-else &> rec)

p-isZero rec = s-isZero <$> (p-tok t-isZero &> rec)
p-fst    rec = s-fst    <$> (p-tok t-fst    &> rec)
p-snd    rec = s-snd    <$> (p-tok t-snd    &> rec)
p-inl    rec = s-inl    <$> (p-tok t-inl    &> rec)
p-inr    rec = s-inr    <$> (p-tok t-inr    &> rec)

p-case rec = s-case <$> (p-tok t-case &> rec)
                    <*> (box (p-tok t-or &> box (p-subexp rec)))

p-λ rec = (λ l⁺ → s-λ (toList l⁺)) <$> (p-tok t-λ &> box (list⁺ p-name) <& box (p-tok t-dot)) <*> rec

p-$ rec = _s-$_ <$> p-subexp rec <*> rec

p-+ rec = chainl1 (p-subexp rec) (box (_s-+_ <$ p-tok t-+))
p-, rec = chainr1 (p-+ rec)      (box (_s-,_ <$ p-tok t-,))
p-∷ rec = chainr1 (p-, rec)      (box (_s-∷_ <$ p-tok t-∷))

p-list rec = (add-nil <$> (p-tok t-[ &> box (chainr1 (p-subexp rec) (box (_s-∷_ <$ p-tok t-,))) <& box (p-tok t-])))
              <|>
              (s-nil <$ p-tok t-[ <& box (p-tok t-])) where
  add-nil : AST → AST
  add-nil (l s-∷ r) = l s-∷ (add-nil r)
  add-nil = _s-∷ s-nil

p-leaf rec = s-leaf <$> (p-tok t-< &> rec <& box (p-tok t->))
p-node rec = _s-node_ <$> p-subexp rec
                      <*> box (p-tok t-| &> box (p-subexp rec))

p-iteℕ rec = p-tok t-iteℕ &> box (s-iteℕ <$> p-subexp rec
                                         <*> box (p-subexp rec)
                                         <*> box (p-subexp rec))

p-iteList rec = p-tok t-iteList &> box (s-iteList <$>      p-subexp rec
                                                  <*> box (p-subexp rec)
                                                  <*> box (p-subexp rec))

p-iteTree rec = p-tok t-iteTree &> box (s-iteTree <$>      p-subexp rec
                                                  <*> box (p-subexp rec)
                                                  <*> box (p-subexp rec))

p-head rec = s-head <$> (p-tok t-head &> rec)
p-tail rec = s-tail <$> (p-tok t-tail &> rec)
p-genStream rec = p-tok t-genStream &> box (s-genStream <$>      p-subexp rec
                                                        <*> box (p-subexp rec)
                                                        <*> box (p-subexp rec))

p-put rec = s-put <$> (p-tok t-put &> rec) <*> (box (p-subexp rec))
p-set rec = s-set <$> (p-tok t-set &> rec)
p-get rec = s-get <$> (p-tok t-get &> rec)
p-genMachine rec = p-tok t-genMachine &> box (s-genMachine <$> p-subexp rec
                                                           <*> box (p-subexp rec)
                                                           <*> box (p-subexp rec)
                                                           <*> box (p-subexp rec))

p-ann rec = s-ann <$> p-subexp rec <*> box (p-tok t-: &> box p-type)

p-subexp rec =
  p-true       <|>
  p-false      <|>
  p-num        <|>
  p-var        <|>
  p-triv       <|>
  p-nil        <|>
  p-leaf   rec <|>
  p-parens rec
-- we list here all nullary nodes because they don't need to be
-- guarded by parentheses, so the user can omit them, e.g., in "10 + 20 + 30"
-- same is true for leaf, because it already has a non-empty prefix, e.g., <42>

p-exp = fix _ $ λ rec →
  p-ann        rec <|>
  p-list       rec <|>
  p-node       rec <|>
  p-$          rec <|>
  p-∷          rec <|>
  p-ite        rec <|>
  p-isZero     rec <|>
  p-fst        rec <|>
  p-snd        rec <|>
  p-inl        rec <|>
  p-inr        rec <|>
  p-case       rec <|>
  p-λ          rec <|>
  p-iteℕ       rec <|>
  p-iteList    rec <|>
  p-iteTree    rec <|>
  p-head       rec <|>
  p-tail       rec <|>
  p-genStream  rec <|>
  p-put        rec <|>
  p-set        rec <|>
  p-get        rec <|>
  p-genMachine rec <|>
  p-subexp     rec

--------------------------------------
-- Parsing

module _ (open Parameters P)
         {{t : Tokenizer (Parameters.Tok P)}}
         {{𝕄 : RawMonadPlus (M)}}
         {{𝕊 : Sized (Parameters.Tok P) Toks}}
         {{𝕃 : ∀ {n} → Subset (theSet (Level.Bounded.Vec (Parameters.Tok P) n)) (theSet (Toks n))}}
         {{ℝ : RawMonadRun M}} where

  private module 𝕄 = RawMonadPlus 𝕄
  private module 𝕃{n} = Subset (𝕃 {n})

  parse_by_ : ∀ {A : Set≤ l} → String → ∀[ Parser P A ] → Maybe (theSet A)
  parse s by parser =
   let input = Vec.fromList $ Tokenizer.fromText t s
       parse = runParser parser (n≤1+n _) (lift $ 𝕃.into input)
       check = λ s → if ⌊ Success.size s Nat.≟ 0 ⌋
                     then just (Success.value s) else nothing
   in case List.TraversableM.mapM MaybeCat.monad check $ runM ℝ parse of λ where
        (just (a ∷ _)) → just (lower a)
        _              → nothing

  parse-exp : String → Maybe AST
  parse-exp s = parse s by p-exp

parse : String → Maybe AST
parse = parse-exp

--------------------------------------
-- Examples (see: Tests/ for more)

private
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  _ : parse "if true" ≡ nothing
  _ = refl

  _ : parse "10 + 20 + 30"   ≡ just (s-num 10 s-+ s-num 20 s-+ s-num 30)
  _ = refl
  _ : parse "(10 + 20) + 30" ≡ just ((s-num 10 s-+ s-num 20) s-+ s-num 30)
  _ = refl
  _ : parse "10 + (20 + 30)" ≡ just (s-num 10 s-+ (s-num 20 s-+ s-num 30))
  _ = refl

  _ : parse "λ f x. if f x then x else 0" ≡ just (s-λ ("f" ∷ "x" ∷ [])
                                                 (s-ite (s-var "f" s-$ s-var "x") (s-var "x") (s-num 0)))
  _ = refl
