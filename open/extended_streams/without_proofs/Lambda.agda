{-# OPTIONS --copatterns #-}

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
  <_> : Ty → Ty
  

infixr 10 _⇒_

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vze : ∀{Γ σ} → Var (Γ < σ) σ
  vsu  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 



data Tm (Γ : Con) : Ty → Set where 
  var  : ∀{σ} → Var Γ σ → Tm Γ σ
  lam  : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app  : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  _,,_ : ∀{σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ∧ τ)
  fst  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ σ
  snd  : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ τ
  ze   : Tm Γ nat
  su   : Tm Γ nat → Tm Γ nat
  rec  : ∀{σ} → Tm Γ σ → Tm Γ (σ ⇒ σ) → Tm Γ nat → Tm Γ σ 
  proj : ∀{σ} → ℕ → Tm Γ < σ > → Tm Γ σ
  tup  : ∀{σ} → (ℕ → Tm Γ σ) → Tm Γ < σ >


mutual 
  data Nf (Γ : Con) : Ty → Set where
    nlam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne   : ∀{σ} → Ne Γ σ → Nf Γ σ
    _,-,_ : ∀{σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ ∧ τ)
    nze : Nf Γ nat
    nsu  : Nf Γ nat → Nf Γ nat
    ntup : ∀{σ}→ (ℕ → Nf Γ σ) → Nf Γ < σ > 
   
  data Ne (Γ : Con) : Ty → Set where
    nvar : ∀{σ} → Var Γ σ → Ne Γ σ
    napp : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    nfst : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ σ
    nsnd : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ τ
    nrec : ∀{σ} → Nf Γ σ  → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ 
    nproj : ∀{σ} → ℕ → Ne Γ < σ > → Ne Γ σ
   

mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (nlam n) = lam (embNf n)
  embNf (ne x) = embNe x
  embNf (a ,-, b) = embNf a ,, embNf b
  embNf nze = ze
  embNf (nsu n) = su (embNf n)
  embNf (ntup f) = tup (λ n → embNf (f n))

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (nvar x) = var x
  embNe (napp t u) = app (embNe t) (embNf u)
  embNe (nfst n) = fst (embNe n)
  embNe (nsnd n) = snd (embNe n)
  embNe (nrec z f n) = rec (embNf z) (embNf f) (embNe n)
  embNe (nproj n s) = proj n (embNe s)


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
wk ρ vze = vze
wk ρ (vsu y) = vsu (ρ y)

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
ren α (su tm) = su (ren α tm)
ren α (rec z f n) = rec (ren α z) (ren α f) (ren α n)
ren α (tup f) = tup (λ n → ren α (f n))
ren α (proj n s) = proj n (ren α s)



mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf α (nlam n) = nlam (renNf (wk α) n)
  renNf α (ne n) = ne (renNe α n)
  renNf α (n ,-, n₁) = renNf α n ,-, renNf α n₁
  renNf α nze = nze
  renNf α (nsu n) = nsu (renNf α n)
  renNf α (ntup f) = ntup (λ n → renNf α (f n))

    
  renNe : ∀{Γ Δ} → Ren Δ Γ → ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe α (nvar x) = nvar (α x)
  renNe α (napp n n') = napp (renNe α n) (renNf α n')
  renNe α (nfst n) = nfst (renNe α n)
  renNe α (nsnd n) = nsnd (renNe α n)
  renNe α (nrec z f n) = nrec (renNf α z) (renNf α f) (renNe α n)
  renNe α (nproj n s) = nproj n (renNe α s) 


-- the identity renaming (maps variables to themselves)
renId : ∀{Γ} → Ren Γ Γ
renId = id


-- composition of renamings (applies two renamings, one after the other)
renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g 


Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f vze     = var vze
lift f (vsu x) = ren vsu (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x) = f x
sub f (lam tm) = lam (sub (lift f) tm)
sub f (app tm tm₁) = app (sub f tm) (sub f tm₁)
sub f (tm ,, tm₁) = sub f tm ,, sub f tm₁
sub f (fst tm) = fst (sub f tm)
sub f (snd tm) = snd (sub f tm)
sub f ze = ze
sub f (su tm) = su (sub f tm)
sub f (rec z fn n) = rec (sub f z) (sub f fn) (sub f n)
sub f (tup g) = tup (λ n → sub f (g n))
sub f (proj n s) = proj n (sub f s) 



subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g



record Stream (A : Set) : Set where
  coinductive
  field head : A
        tail : Stream A

open Stream


lookup : ∀{A} → (s : Stream A) → (ℕ → A)
lookup s zero = head s
lookup s (suc n) = lookup (tail s) n

tabulate : ∀{A} → (ℕ → A) → Stream A
head (tabulate f) = f zero
tail (tabulate f) = tabulate (λ n → f (suc n))  


Val : Con → Ty → Set
Val Γ ι = Nf Γ ι
Val Γ nat = Nf Γ nat
Val Γ (σ ⇒ τ) = ∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ 
Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ
Val Γ < σ > = Stream (Val Γ σ)

renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
renval {σ = ι} α x = renNf α x
renval {σ = nat} α n = renNf α n
renval {σ = σ ⇒ τ} α v = λ {E} β v' → v (renComp β α) v'
renval {σ = σ ∧ τ} α v = renval {σ = σ} α (proj₁ v) , renval {σ = τ} α (proj₂ v)
head (renval {Γ} {Δ} {< σ >} α s) = renval {σ = σ} α (head s)
tail (renval {Γ} {Δ} {< σ >} α s) = renval {σ = < σ >} α (tail s)


Env : Con → Con → Set
Env Γ Δ = ∀{σ} → Var Γ σ → Val Δ σ


_<<_ : ∀{Γ Δ} → Env Γ Δ → ∀{σ} → Val Δ σ → Env (Γ < σ) Δ
(γ << v) vze = v
(γ << v) (vsu x) = γ x 

-- notice that I have written it with 3 explicit arguments rather than
-- two, this is because Env computes to:

-- ∀{Γ} → (∀{σ} → Var Γ σ → Val σ) → ∀{σ} → Val σ → ∀{σ'} → 
-- Var (Γ < σ) σ' → Val σ'

-- which has three explicit arguments.

-- Notice also that the definition of _<<_ looks a bit like lookup ,
-- this is because the new definition of Env is a lookup function in a
-- way, so to define a new longer environment we need to explain how
-- to lockup variables in it.


renenv : ∀{Γ Δ E} → Ren Δ E → Env Γ Δ → Env Γ E
renenv {ε} α γ ()
renenv {Γ < σ} α γ vze = renval {σ = σ} α (γ vze)
renenv {Γ < σ} α γ (vsu x) = renenv α (γ ∘ vsu) x 


mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι x = x
  reify nat x = x
  reify (σ ⇒ τ) x = nlam (reify τ (x vsu (reflect σ (nvar vze))))
  reify (σ ∧ τ) x = reify σ (proj₁ x) ,-, reify τ (proj₂ x)
  reify < σ > s = ntup (λ n → reify σ (lookup s n))

  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι v = ne v
  reflect nat n = ne n
  reflect (σ ⇒ τ) n = λ α v → reflect τ (napp (renNe α n) (reify σ v))
  reflect (σ ∧ τ) n = (reflect σ (nfst n)) , (reflect τ (nsnd n))
  reflect < σ > xs = tabulate (λ n → reflect σ (nproj n xs)) 

 
natfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
natfold {σ = σ} z f (ne x) = reflect σ (nrec (reify _ z) (reify (_ ⇒ _) f) x)
natfold {σ = σ} z f nze = z
natfold {σ = σ} z f (nsu n) = f id (natfold {σ = σ} z f n)


mutual
  eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
  eval γ (var x) = γ x
  eval γ (lam t) = λ α v → eval (renenv α γ << v) t
  eval γ (app t u) = eval γ t renId (eval γ u)
  eval γ (tm ,, tm₁) = eval γ tm , eval γ tm₁
  eval γ (fst tm) = proj₁ (eval γ tm)
  eval γ (snd tm) = proj₂ (eval γ tm)
  eval γ ze = nze
  eval γ (su tm) = nsu (eval γ tm)
  eval {σ = σ} γ (rec z f n) = natfold {σ = σ} (eval γ z) (eval γ f) (eval γ n)
  eval γ (tup {σ = σ} f) = tabulate (λ n → eval γ (f n))
  eval γ (proj n s) = lookup (eval γ s) n 


idE : ∀{Γ} → Env Γ Γ
idE {ε} ()
idE {Γ < σ} vze = reflect σ (nvar vze)
idE {Γ < τ} (vsu {σ = σ}{τ = .τ} x) = renval {σ = σ} vsu (idE {Γ} x) 

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)


