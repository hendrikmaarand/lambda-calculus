{-# OPTIONS --copatterns --termination-depth=3 #-}

module Lambda where

open import Data.Bool hiding (_∧_)
open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_<_; fold)
open import Data.List hiding ([_]; unfold)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  ι   : Ty
  nat : Ty
  _⇒_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty
  [_] : Ty → Ty
  

infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  zero : ∀{Γ σ} → Var (Γ < σ) σ
  suc  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 



data Tm (Γ : Con) : Ty → Set where 
  var  : ∀{σ} → Var Γ σ → Tm Γ σ
  lam  : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app  : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  _,,_ : ∀{σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ∧ τ)
  fst  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ σ
  snd  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ τ
  ze   : Tm Γ nat
  sc   : Tm Γ nat → Tm Γ nat
  rec  : ∀{σ} → Tm Γ σ → Tm Γ (σ ⇒ σ) → Tm Γ nat → Tm Γ σ 
  hd   : ∀{σ} → Tm Γ [ σ ] → Tm Γ σ
  tl   : ∀{σ} → Tm Γ [ σ ] → Tm Γ [ σ ]
  unfold : ∀{σ} → Tm Γ (nat ⇒ σ) → Tm Γ [ σ ]


mutual 
  data Nf (Γ : Con) : Ty → Set where
    lam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne   : ∀{σ} → Ne Γ σ → Nf Γ σ
    _,,_ : ∀{σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ ∧ τ)
    zero : Nf Γ nat
    suc  : Nf Γ nat → Nf Γ nat
    unfold : ∀{σ}→ Nf Γ (nat ⇒ σ) → Nf Γ [ σ ] 
   
  data Ne (Γ : Con) : Ty → Set where
    var : ∀{σ} → Var Γ σ → Ne Γ σ
    app : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    fst : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ σ
    snd : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ τ
    rec : ∀{σ} → Nf Γ σ  → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ 
    hd : ∀{σ} → Ne Γ [ σ ] → Ne Γ σ
    tl : ∀{σ} → Ne Γ [ σ ] → Ne Γ [ σ ]

  record ∞Nf-stream (Γ : Con)(σ : Ty) : Set where
    coinductive
    field nforce : Nf Γ [ σ ]

open ∞Nf-stream
    


-- the type of renamings: functions mapping variables in one context to
-- variables in another

Ren : Con → Con → Set
Ren Δ Γ = ∀{σ} → Var Δ σ → Var Γ σ

-- We are working towards substitution - the operation of replacing
-- variables by terms in a term. First we'll look at renaming which is
-- a simpler function that replaces variables by variables.


-- weakening, takes a existing renaming ρ, and adds a new 0
-- variable. 0 is mapped to 0, for everything else the ρ renaming is
-- used and then incremented by 1.

wk : ∀{Γ Δ σ} → Ren Δ Γ → Ren (Δ < σ) (Γ < σ)
wk ρ zero = zero
wk ρ (suc y) = suc (ρ y)

-- apply a renaming to a term, wk is needed to push the renaming inside 
-- a lambda term. i.e. lambda binds a new variable 0, we don't want to
-- change that but we want to rename any other variables in the body.


ren : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Tm Δ σ → Tm Γ σ
ren α (var x) = var (α x)
ren α (lam tm) = lam (ren (wk α) tm)
ren α (app tm tm₁) = app (ren α tm) (ren α tm₁)
ren α (tm ,, tm₁) = ren α tm ,, ren α tm₁
ren α (fst tm) = fst (ren α tm)
ren α (snd tm) = snd (ren α tm)
ren α ze = ze
ren α (sc tm) = sc (ren α tm)
ren α (rec z f n) = rec (ren α z) (ren α f) (ren α n)
ren α (hd s) = hd (ren α s)
ren α (tl s) = tl (ren α s)
ren α (unfold f) = unfold (ren α f)




mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf α (lam n) = lam (renNf (wk α) n)
  renNf α (ne n) = ne (renNe α n)
  renNf α (n ,, n₁) = renNf α n ,, renNf α n₁
  renNf α zero = zero
  renNf α (suc n) = suc (renNf α n)
  renNf α (unfold f) = unfold (renNf α f) --unfold (renNf α z) (renNf α f)

    
  renNe : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe α (var x) = var (α x)
  renNe α (app n n') = app (renNe α n) (renNf α n')
  renNe α (fst n) = fst (renNe α n)
  renNe α (snd n) = snd (renNe α n)
  renNe α (rec z f n) = rec (renNf α z) (renNf α f) (renNe α n)
  renNe α (hd s) = hd (renNe α s) 
  renNe α (tl s) = tl (renNe α s)

  renNf∞ : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → ∞Nf-stream Δ σ → ∞Nf-stream Γ σ
  nforce (renNf∞ α n) = renNf α (nforce n) 


-- the identity renaming (maps variables to themselves)
renId : ∀{Γ} → Ren Γ Γ
renId = id


-- composition of renamings (applies two renamings, one after the other)
renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g 


Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f zero     = var zero
lift f (suc x) = ren suc (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x) = f x
sub f (lam tm) = lam (sub (lift f) tm)
sub f (app tm tm₁) = app (sub f tm) (sub f tm₁)
sub f (tm ,, tm₁) = sub f tm ,, sub f tm₁
sub f (fst tm) = fst (sub f tm)
sub f (snd tm) = snd (sub f tm)
sub f ze = ze
sub f (sc tm) = sc (sub f tm)
sub f (rec z fn n) = rec (sub f z) (sub f fn) (sub f n)
sub f (hd s) = hd (sub f s)
sub f (tl s) = tl (sub f s)
sub f (unfold fn) = unfold (sub f fn)



subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

mutual
  data StreamVal (A B : Set) : Set where
    ne : B → StreamVal A B
    streamSV : A → ∞StreamVal A B → StreamVal A B

  record ∞StreamVal (A B : Set) : Set where
    coinductive
    field vforce : StreamVal A B

open ∞StreamVal


record _∞∼_ {A B}(s s' : ∞StreamVal A B) : Set where
  coinductive
  field ∼force : vforce s ≅ vforce s'
open _∞∼_


mutual
  map∞SV : ∀{A B C D} → (A → C) → (B → D) → ∞StreamVal A B → ∞StreamVal C D
  vforce (map∞SV f g s) = mapSV f g (vforce s)

  mapSV : ∀{A B C D} → (A → C) → (B → D) → StreamVal A B → StreamVal C D
  mapSV f g (ne x) = ne (g x)
  mapSV f g (streamSV h t) = streamSV (f h) (map∞SV f g t)



Val : Con → Ty → Set
Val Γ ι = Nf Γ ι
Val Γ nat = Nf Γ nat
Val Γ (σ ⇒ τ) = ∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ
Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ
Val Γ [ σ ] = StreamVal (Val Γ σ) (Ne Γ [ σ ])


Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) zero = v
(γ << v) (suc x) = γ x 

-- notice that I have written it with 3 explicit arguments rather than
-- two, this is because Env computes to:

-- ∀{Γ} → (∀{σ} → Var Γ σ → Val σ) → ∀{σ} → Val σ → ∀{σ'} → 
-- Var (Γ < σ) σ' → Val σ'

-- which has three explicit arguments.

-- Notice also that the definition of _<<_ looks a bit like lookup ,
-- this is because the new definition of Env is a lookup function in a
-- way, so to define a new longer environment we need to explain how
-- to lockup variables in it.


renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
renval {Γ} {Δ} {ι} α x = renNf α x
renval {Γ} {Δ} {nat} α n = renNf α n
renval {Γ} {Δ} {σ ⇒ τ} α v = λ {E} β v' → v (renComp β α) v'
renval {Γ} {Δ} {σ ∧ τ} α v = renval {σ = σ} α (proj₁ v) , renval {σ = τ} α (proj₂ v)
renval {Γ} {Δ} {[ σ ]} α s = mapSV  (renval {σ = σ} α) (renNe α) s



renenv : ∀{Γ Δ E} → Ren Δ E → Env Γ Δ → Env Γ E
renenv {ε} α γ ()
renenv {Γ < σ} α γ zero = renval {_} {_} {σ} α (γ zero)
renenv {Γ < σ} α γ (suc x) = renenv α (γ ∘ suc) x 



mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι x = x
  reify nat x = x
  reify (σ ⇒ τ) x = lam (reify τ (x suc (reflect σ (var zero))))
  reify (σ ∧ τ) x = reify σ (proj₁ x) ,, reify τ (proj₂ x)
  reify [ σ ] (ne x) = ne x
  reify [ σ ] (streamSV h t) = unfold (reify (nat ⇒ σ) (fold (streamSV h t)))

  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι v = ne v
  reflect nat n = ne n
  reflect (σ ⇒ τ) n = λ α v → reflect τ (app (renNe α n) (reify σ v))
  reflect (σ ∧ τ) n = reflect σ (fst n) , reflect τ (snd n)
  reflect [ σ ] xs = ne xs
  
  ∞reify : ∀{Γ σ} → ∞StreamVal (Val Γ σ) (Ne Γ [ σ ]) → ∞Nf-stream Γ σ
  nforce (∞reify s) = reify _ (vforce s)

  fold : ∀{Γ σ} → StreamVal (Val Γ σ) (Ne Γ [ σ ]) → Val Γ (nat ⇒ σ)
  fold {Γ}{σ = σ} s {Γ'} ρ n = 
    natfold {σ = [ σ ] ⇒ σ} 
      (λ {Δ}(ρ' : Ren Γ' Δ) s → head s)
      (λ {Δ}(ρ' : Ren Γ' Δ) (f : Val _ ([ σ ] ⇒ σ)){Δ'} (ρ'' : Ren Δ Δ') s' →
                f ρ'' (tail s')) 
      n 
      id (renval {σ = [ σ ]} ρ s)


  head : ∀{Γ σ} → StreamVal (Val Γ σ) (Ne Γ [ σ ]) → Val Γ σ
  head (ne x) = reflect _ (hd x)
  head (streamSV h t) = h

  tail : ∀{Γ σ} → StreamVal (Val Γ σ) (Ne Γ [ σ ]) → Val Γ [ σ ]
  tail (ne x) = reflect _ (tl x)
  tail (streamSV h t) = vforce t 

  natfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
  natfold {σ = σ} z f (ne x) = reflect σ (rec (reify _ z) (reify (_ ⇒ _) f) x)
  natfold {σ = σ} z f zero = z
  natfold {σ = σ} z f (suc n) = f id (natfold {σ = σ} z f n) 



mutual
  unFold : ∀{Γ σ} → (f : Val Γ (nat ⇒ σ)) → StreamVal (Val Γ σ) (Ne Γ [ σ ])
  unFold f = streamSV (f renId zero) (∞unFold (λ α n → f α (suc n)))

  ∞unFold : ∀{Γ σ} → (f : Val Γ (nat ⇒ σ)) → ∞StreamVal (Val Γ σ) (Ne Γ [ σ ])
  vforce (∞unFold f) = unFold f


mutual
  eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var x) = γ x
  eval γ (lam tm) = λ α v → eval (renenv α γ << v) tm
  eval γ (app tm tm₁) = eval γ tm renId (eval γ tm₁)
  eval γ (tm ,, tm₁) = eval γ tm , eval γ tm₁
  eval γ (fst tm) = proj₁ (eval γ tm)
  eval γ (snd tm) = proj₂ (eval γ tm)
  eval γ ze = zero
  eval γ (sc tm) = suc (eval γ tm)
  eval {σ = σ} γ (rec z f n) = natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)
  eval γ (hd s) = head (eval γ s)
  eval γ (tl s) = tail (eval γ s)
  eval γ (unfold {σ = σ} f) = unFold (eval γ f)


idE : ∀{Γ} → Env Γ Γ
idE {ε} ()
idE {Γ < σ} zero = reflect σ (var zero)
idE {Γ < τ} (suc {σ = σ}{τ = .τ} x) = renval {σ = σ} suc (idE {Γ} x) 

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)


