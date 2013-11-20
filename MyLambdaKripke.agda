module MyLambdaKripke where

open import Data.Bool hiding (_∧_)
open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (_<_)
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  nat : Ty
  _⇒_ : Ty → Ty → Ty
  _∧_ : Ty → Ty → Ty 

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


mutual 
  data Nf (Γ : Con) : Ty → Set where
    lam  : ∀{σ τ} → Nf (Γ < σ) τ → Nf Γ (σ ⇒ τ)
    ne   : Ne Γ nat → Nf Γ nat
    _,,_ : ∀{σ τ} → Nf Γ σ → Nf Γ τ → Nf Γ (σ ∧ τ)
    zero : Nf Γ nat
    suc  : Nf Γ nat → Nf Γ nat
   
  data Ne (Γ : Con) : Ty → Set where
    var : ∀{σ} → Var Γ σ → Ne Γ σ
    app : ∀{σ τ} → Ne Γ (σ ⇒ τ) → Nf Γ σ → Ne Γ τ
    fst : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ σ
    snd : ∀{σ τ} → Ne Γ (σ ∧ τ) → Ne Γ τ
    rec : ∀{σ} → Nf Γ σ  → Nf Γ (σ ⇒ σ) → Ne Γ nat → Ne Γ σ 
    nsuc : Nf Γ nat → Ne Γ nat
    


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
ren ρ (var x) = var (ρ x)
ren ρ (lam tm) = lam (ren (wk ρ) tm)
ren ρ (app tm tm₁) = app (ren ρ tm) (ren ρ tm₁)
ren ρ (tm ,, tm₁) = ren ρ tm ,, ren ρ tm₁
ren ρ (fst tm) = fst (ren ρ tm)
ren ρ (snd tm) = snd (ren ρ tm)
ren ρ ze = ze
ren ρ (sc tm) = sc (ren ρ tm)
ren ρ (rec z f n) = rec (ren ρ z) (ren ρ f) (ren ρ n)


mutual
  renNf : ∀{Γ Δ} → Ren Δ Γ →  ∀{σ} → Nf Δ σ → Nf Γ σ
  renNf ρ (lam n) = lam (renNf (wk ρ) n)
  renNf ρ (ne n) = ne (renNe ρ n)
  renNf ρ (n ,, n₁) = renNf ρ n ,, renNf ρ n₁
  renNf ρ zero = zero
  renNf ρ (suc n) = suc (renNf ρ n)
    
  renNe : ∀{Γ Δ} → Ren Δ Γ →  ∀{σ} → Ne Δ σ → Ne Γ σ
  renNe ρ (var x) = var (ρ x)
  renNe ρ (app n n') = app (renNe ρ n) (renNf ρ n')
  renNe ρ (fst n) = fst (renNe ρ n)
  renNe ρ (snd n) = snd (renNe ρ n)
  renNe ρ (rec z f n) = rec (renNf ρ z) (renNf ρ f) (renNe ρ n)
  renNe ρ (nsuc n) = nsuc (renNf ρ n)
  
  
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



subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g


Val : Con → Ty → Set
Val Γ nat = Nf Γ nat
Val Γ (σ ⇒ τ) = ∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ
Val Γ (σ ∧ τ) = Val Γ σ × Val Γ τ


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
renval {Γ} {Δ} {nat} α x = renNf α x
renval {Γ} {Δ} {σ ⇒ τ} α v = λ {E} β v' → v (renComp β α) v'
renval {Γ} {Δ} {σ ∧ τ} α v = renval α (proj₁ v) , renval α (proj₂ v)


renenv : ∀{Γ Δ E} → Ren Δ E → Env Γ Δ → Env Γ E
renenv {ε} α γ ()
renenv {Γ < σ} α γ zero = renval {_} {_} {σ} α (γ zero)
renenv {Γ < σ} α γ (suc x) = renenv α (γ ∘ suc) x 


mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify nat x = x
  reify (σ ⇒ τ) v = lam (reify τ (v suc (reflect σ (var zero))))
  reify (σ ∧ τ) v = reify σ (proj₁ v) ,, reify τ (proj₂ v) 

  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect nat n = ne n
  reflect (σ ⇒ τ) n = λ α v → reflect τ (app (renNe α n) (reify σ v))
  reflect (σ ∧ τ) n = reflect σ (fst n) , reflect τ (snd n)

nfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
nfold z f (ne x) = reflect _ (rec (reify _ z) (reify (_ ⇒ _) f) x)
nfold z f zero = z
nfold z f (suc n) = f id (nfold z f n) 


eval : ∀{Γ Δ σ} → Env Γ Δ → Tm Γ σ → Val Δ σ
eval γ (var x) = γ x
eval γ (lam tm) = λ α v → eval (renenv α γ << v) tm
eval γ (app tm tm₁) = eval γ tm renId (eval γ tm₁)
eval γ (tm ,, tm₁) = eval γ tm , eval γ tm₁
eval γ (fst tm) = proj₁ (eval γ tm)
eval γ (snd tm) = proj₂ (eval γ tm)
eval γ ze = zero
eval γ (sc tm) = suc (eval γ tm)
eval γ (rec z f n) = nfold (eval γ z) (eval γ f) (eval γ n)


idE : ∀{Γ} → Env Γ Γ
idE {ε} ()
idE {Γ < σ} zero = reflect σ (var zero)
idE {Γ < σ} (suc x) = renval suc (idE {Γ} x) 

norm : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
norm t = reify _ (eval idE t)

