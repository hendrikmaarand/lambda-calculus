module Lambda where

open import Data.Bool hiding (_∧_; _∨_)
open import Function
open import Data.Nat hiding (_<_;_+_)
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)


data Ty : Set where
  bool : Ty
  nat : Ty
  _∧_ : Ty → Ty → Ty
  _∨_ : Ty → Ty → Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  zero : ∀{Γ σ} → Var (Γ < σ) σ
  suc  : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ 

data Tm (Γ : Con) : Ty → Set where
  tr  : Tm Γ bool
  fls : Tm Γ bool
  ifthenelse : ∀{σ} → Tm Γ bool → Tm Γ σ → Tm Γ σ → Tm Γ σ
  zero  : Tm Γ nat
  suc   : Tm Γ nat → Tm Γ nat
  rec   : ∀{σ} → Tm Γ σ → Tm Γ (σ ⇒ σ) → Tm Γ nat → Tm Γ σ 
  _,,_  : ∀{σ τ} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ∧ τ)
  fst   : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ σ
  snd   : ∀{σ τ} → Tm Γ (σ ∧ τ) → Tm Γ τ 
  case  : ∀{σ τ ρ} → Tm Γ (σ ⇒ ρ) → Tm Γ (τ ⇒ ρ) → Tm Γ (σ ∨ τ) → Tm Γ ρ
  left  : ∀{σ τ} → Tm Γ σ → Tm Γ (σ ∨ τ)
  right : ∀{σ τ} → Tm Γ τ → Tm Γ (σ ∨ τ)
  var   : ∀{σ} → Var Γ σ → Tm Γ σ
  lam   : ∀{σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
  app   : ∀{σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ

Val : Ty → Set
Val bool = Bool
Val nat = ℕ
Val (σ ∧ τ) = Val σ × Val τ
Val (σ ∨ τ) = Val σ ⊎ Val τ 
Val (σ ⇒ τ) = Val σ → Val τ


Env : Con → Set
Env Γ = ∀{σ} → Var Γ σ → Val σ


_<<_ : ∀{Γ} → Env Γ → ∀{σ} → Val σ → Env (Γ < σ)
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
-- to lookup variables in it.



eval : ∀{Γ σ} → Env Γ → Tm Γ σ → Val σ
eval γ tr  = true
eval γ fls = false
eval γ (ifthenelse a b1 b2) = if (eval γ a) then (eval γ b1) else (eval γ b2)
eval γ zero    = zero
eval γ (suc n) = suc (eval γ n)
eval γ (rec z f n) = fold (eval γ z) (eval γ f) (eval γ n) 
eval γ (x ,, y)   = eval γ x , eval γ y
eval γ (fst tm)   = proj₁ (eval γ tm)
eval γ (snd tm)   = proj₂ (eval γ tm)
eval γ (left tm)  = inj₁ (eval γ tm)
eval γ (right tm) = inj₂ (eval γ tm)
eval γ (case tm tm1 tm2) = [ eval γ tm , eval γ tm1 ]′ (eval γ tm2)
eval γ (var t) = γ t
eval γ (lam t) = λ x → eval (γ << x) t
eval γ (app t t') = eval γ t (eval γ t')


-- We are working towards substitution - the operation of replacing
-- variables by terms in a term. First we'll look at renaming which is
-- a simpler function that replaces variables by variables.

-- the type of renamings: functions mapping variables in one context to
-- variables in another

Ren : Con → Con → Set
Ren Δ Γ = ∀{σ} → Var Δ σ → Var Γ σ

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
ren ρ tr  = tr
ren ρ fls = fls
ren ρ (ifthenelse t u v) = ifthenelse (ren ρ t) (ren ρ u) (ren ρ v)
ren ρ zero    = zero
ren ρ (suc n) = suc (ren ρ n)
ren ρ (rec z f n) = rec (ren ρ z) (ren ρ f) (ren ρ n) 
ren ρ (tm ,, tm₁) = ren ρ tm ,, ren ρ tm₁
ren ρ (fst tm) = fst (ren ρ tm)
ren ρ (snd tm) = snd (ren ρ tm)
ren ρ (case tm tm₁ tm₂) = case (ren ρ tm) (ren ρ tm₁) (ren ρ tm₂)
ren ρ (left tm) = left (ren ρ tm)
ren ρ (right tm) = right (ren ρ tm)
ren ρ (var y) = var (ρ y)
ren ρ (lam y) = lam (ren (wk ρ) y)
ren ρ (app y y') = app (ren ρ y) (ren ρ y')



-- the identity renaming (maps variables to themselves)

renId : ∀{Γ} → Ren Γ Γ
renId = id

-- composition of renamings (applies two renamings, one after the other)

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g

postulate ext : {A : Set}{B B' : A → Set}{f : ∀ a → B a}{g : ∀ a → B' a} →
                (∀ a → f a ≅ g a) → f ≅ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀{a} → B a}{g : ∀{a} → B' a} → 
               (∀ a → f {a} ≅ g {a}) → 
               _≅_ {_}{ {a : A} → B a} f {_}{ {a : A} → B' a} g


-- if you weaken the identity renaming then it should still be the same thing
wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≅ renId x
wkid zero = refl
wkid (suc y) = refl

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x y → C x y → Set d}
          {x y z u v w}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ u → y ≅ v → z ≅ w  → f x y z ≅ f u v w
cong₃ f refl refl refl = refl


-- if you rename a terms using the id renaming, then the term shouldn't change
renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≅  t
renid tr = refl
renid fls = refl
renid (ifthenelse t u v) = cong₃ ifthenelse (renid t) (renid u) (renid v)
renid zero = refl
renid (suc n) = cong {B = λ _ → Tm _ nat} suc (renid n) 
renid (rec z f n) = cong₃ rec (renid z) (renid f) (renid n)
renid (tm ,, tm₁) = cong₂ _,,_ (renid tm) (renid tm₁)
renid (fst tm) = cong fst (renid tm)
renid (snd tm) = cong snd (renid tm)
renid (case tm tm₁ tm₂) = cong₃ case (renid tm) (renid tm₁) (renid tm₂)
renid (left tm) = cong left (renid tm)
renid (right tm) = cong right (renid tm)
renid (var y) = refl
renid (lam y) = cong lam (trans (cong (λ (f : Ren _ _) → ren f y) 
                                       (iext (λ _ → ext wkid))) 
                                (renid y))
renid (app y y') = cong₂ app (renid y) (renid y') 


-- composing two renamings and then weakening them together should be
-- the same as weakening them individually and then composing them
wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≅ renComp (wk f) (wk g) x  
wkcomp f g zero = refl
wkcomp f g (suc y) = refl

-- composing renamings and then applying them, should be the same as
-- applying them individually
rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≅ (ren f ∘ ren g) t
rencomp f g tr = refl
rencomp f g fls = refl
rencomp f g (ifthenelse t u v) = cong₃ ifthenelse (rencomp f g t) (rencomp f g u) (rencomp f g v) 
rencomp f g zero = refl
rencomp f g (suc n) = cong {B = λ _ → Tm _ nat} suc (rencomp f g n)
rencomp f g (rec z f' n) = cong₃ rec (rencomp f g z) (rencomp f g f') (rencomp f g n)
rencomp f g (tm ,, tm₁) = cong₂  _,,_ (rencomp f g tm) (rencomp f g tm₁)
rencomp f g (fst tm) = cong fst (rencomp f g tm)
rencomp f g (snd tm) = cong snd (rencomp f g tm)
rencomp f g (case tm tm₁ tm₂) = cong₃ case (rencomp f g tm) (rencomp f g tm₁) (rencomp f g tm₂)
rencomp f g (left tm) = cong left (rencomp f g tm)
rencomp f g (right tm) = cong right (rencomp f g tm)
rencomp f g (var y) = refl
rencomp f g (lam y) = cong lam (trans (cong (λ (f : Ren _ _) → ren f y)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) y))
rencomp f g (app y y') = cong₂ app (rencomp f g y ) (rencomp f g y' )


Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f zero     = var zero
lift f (suc x) = ren suc (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f tr = tr
sub f fls = fls
sub f (ifthenelse t u v) = ifthenelse (sub f t) (sub f u) (sub f v)
sub f zero = zero
sub f (suc n) = suc (sub f n)
sub f (rec z f' n) = rec (sub f z) (sub f f') (sub f n)
sub f (tm ,, tm₁) = sub f tm ,, sub f tm₁
sub f (fst tm) = fst (sub f tm)
sub f (snd tm) = snd (sub f tm)
sub f (case tm tm₁ tm₂) = case (sub f tm) (sub f tm₁) (sub f tm₂)
sub f (left tm) = left (sub f tm )
sub f (right tm) = right (sub f tm)
sub f (var y) = f y
sub f (lam y) = lam (sub (lift f) y)
sub f (app y y') = app (sub f y) (sub f y')


subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≅ subId x
liftid zero = refl
liftid (suc y) = refl



subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≅ id t
subid tr = refl
subid fls = refl
subid (ifthenelse t u v) = cong₃ ifthenelse (subid t) (subid u) (subid v)
subid zero = refl
subid (suc n) = cong {B = λ _ → Tm _ nat} suc (subid n)
subid (rec z f n) = cong₃ rec (subid z) (subid f) (subid n)
subid (tm ,, tm₁) = cong₂ _,,_ (subid tm) (subid tm₁)
subid (fst tm) = cong fst (subid tm)
subid (snd tm) = cong snd (subid tm)
subid (case tm tm₁ tm₂) = cong₃ case (subid tm) (subid tm₁) (subid tm₂)
subid (left tm) = cong left (subid tm)
subid (right tm) = cong right (subid tm)
subid (var x)   = refl
subid (app t u) = cong₂ app (subid t) (subid u)
subid (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))



-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≅ lift (f ∘ g) x
liftwk f g zero = refl
liftwk f g (suc y) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≅ sub (f ∘ g) t
subren f g tr = refl
subren f g fls = refl
subren f g (ifthenelse t u v) = cong₃ ifthenelse (subren f g t) (subren f g u) (subren f g v) 
subren f g zero = refl
subren f g (suc n) = cong Tm.suc (subren f g n)
subren f g (rec z f' n) = cong₃ rec (subren f g z) (subren f g f') (subren f g n)
subren f g (tm ,, tm₁) = cong₂ _,,_ (subren f g tm) (subren f g tm₁)
subren f g (fst tm) = cong fst (subren f g tm)
subren f g (snd tm) = cong snd (subren f g tm)
subren f g (case tm tm₁ tm₂) = cong₃ case (subren f g tm) (subren f g tm₁) (subren f g tm₂)
subren f g (left tm) = cong left (subren f g tm)
subren f g (right tm) = cong right (subren f g tm)
subren f g (var x)   = refl
subren f g (app t u) = cong₂ app (subren f g t) (subren f g u)
subren f g (lam t)   = cong lam (trans (subren (lift f) (wk g) t)
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))


renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≅ lift (ren f ∘ g) x
renwklift f g zero    = refl
renwklift f g (suc x) = trans (sym (rencomp (wk f) suc (g x))) (rencomp suc f (g x)) 

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘  sub g) t ≅ sub (ren f ∘ g) t
rensub f g tr = refl
rensub f g fls = refl
rensub f g (ifthenelse t u v) = cong₃ ifthenelse (rensub f g t) (rensub f g u) (rensub f g v) 
rensub f g zero = refl
rensub f g (suc n) = cong Tm.suc (rensub f g n)
rensub f g (rec z f' n) = cong₃ rec (rensub f g z) (rensub f g f') (rensub f g n)
rensub f g (tm ,, tm₁) = cong₂ _,,_ (rensub f g tm) (rensub f g tm₁)
rensub f g (fst tm) = cong fst (rensub f g tm)
rensub f g (snd tm) = cong snd (rensub f g tm)
rensub f g (case tm tm₁ tm₂) = cong₃ case (rensub f g tm) (rensub f g tm₁) (rensub f g tm₂)
rensub f g (left tm) = cong left (rensub f g tm)
rensub f g (right tm) = cong right (rensub f g tm)
rensub f g (var x)   = refl
rensub f g (app t u) = cong₂ app (rensub f g t) (rensub f g u)
rensub f g (lam t)   = cong lam (trans (rensub (wk f) (lift g) t) 
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))


liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≅ subComp (lift f) (lift g) x
liftcomp f g zero    = refl
liftcomp f g (suc x) = 
  proof 
  lift (subComp f g) (suc x) 
  ≅⟨ rensub suc f (g x) ⟩
  sub (ren suc ∘ f) (g x)
  ≅⟨ sym (subren (lift f) suc (g x)) ⟩
  subComp (lift f) (lift g) (suc x) 
  ∎

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≅ (sub f ∘ sub g) t
subcomp f g tr = refl
subcomp f g fls = refl
subcomp f g (ifthenelse t u v) = cong₃ ifthenelse (subcomp f g t) (subcomp f g u) (subcomp f g v) 
subcomp f g zero = refl
subcomp f g (suc n) = cong Tm.suc (subcomp f g n)
subcomp f g (rec z f' n) = cong₃ rec (subcomp f g z) (subcomp f g f') (subcomp f g n)
subcomp f g (tm ,, tm₁) = cong₂ _,,_ (subcomp f g tm) (subcomp f g tm₁)
subcomp f g (fst tm) = cong fst (subcomp f g tm)
subcomp f g (snd tm) = cong snd (subcomp f g tm)
subcomp f g (case tm tm₁ tm₂) = cong₃ case (subcomp f g tm) (subcomp f g tm₁) (subcomp f g tm₂)
subcomp f g (left tm) = cong left (subcomp f g tm)
subcomp f g (right tm) = cong right (subcomp f g tm)
subcomp f g (var x)   = refl
subcomp f g (app t u) = cong₂ app (subcomp f g t) (subcomp f g u)
subcomp f g (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                              (iext λ _ → ext (liftcomp f g))) 
                                        (subcomp (lift f) (lift g) t))



wk<< : ∀{Γ Δ}(α : Ren Γ Δ)(β : Env Δ){σ}(v : Val σ) → ∀{ρ}(y : Var(Γ < σ) ρ) → ((β ∘ α) << v) y ≅ ((β << v) ∘ wk α) y
wk<< α β v zero = proof v ≡⟨⟩ v ∎
wk<< α β v (suc y) = proof β (α y) ≡⟨⟩ β (α y) ∎

reneval : ∀{Γ Δ σ}(α : Ren Γ Δ)(β : Env Δ)(t : Tm Γ σ) → eval (β ∘ α) t ≅ (eval β ∘ ren α) t
reneval α β tr = refl
reneval α β fls = refl
reneval α β (ifthenelse t u v) = cong₃ if_then_else_ (reneval α β t) (reneval α β u) (reneval α β v) 
reneval α β zero = refl
reneval α β (suc n) = cong ℕ.suc (reneval α β n)
reneval α β (rec z f n) = cong₃ fold (reneval α β z) (reneval α β f) (reneval α β n)
reneval α β (tm ,, tm₁) = cong₂ _,_ (reneval α β tm) (reneval α β tm₁)
reneval α β (fst tm) = cong proj₁ (reneval α β tm)
reneval α β (snd tm) = cong proj₂ (reneval α β tm)
reneval {Γ} {Δ} α β (case {σ}{τ}{ρ} tm tm₁ tm₂) =
  proof
  --[ eval (β ∘ α)  tm , eval (β ∘ α) tm₁ ] (eval (β ∘ α) tm₂)
  [_,_] {C = λ _ → Val ρ} (eval (β ∘ α)  tm) (eval (β ∘ α) tm₁) (eval (β ∘ α) tm₂)
  ≅⟨ cong₂ _$_ (cong₂ ([_,_] {C = λ _ → Val ρ}) (reneval {Γ} {Δ} α β tm) (reneval {Γ} {Δ} α β tm₁)) (reneval {Γ} {Δ} α β tm₂) ⟩
  [_,_] {C = λ _ → Val ρ} (eval β (ren α tm))(eval β (ren α tm₁)) (eval β (ren α tm₂))
  ∎ 
reneval α β (left tm) = cong inj₁ (reneval α β tm)
reneval α β (right tm) = cong inj₂ (reneval α β tm)
reneval α β (var x) = proof β (α x) ≡⟨⟩ β (α x) ∎
reneval α β (lam t) = ext λ v →
  proof
  eval ((β ∘ α) << v) t 
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ σ → ext λ x → wk<< α β v x) ⟩
  eval ((β << v) ∘ (wk α)) t
  ≅⟨ reneval (wk α) (β << v) t ⟩
  eval (β << v) (ren (wk α) t)
  ∎
reneval α β (app t u) = 
  proof
  eval (β ∘ α) t (eval (β ∘ α) u) 
  ≅⟨ cong₂ _$_ (reneval α β t) (reneval α β u) ⟩
  eval β (ren α t) (eval β (ren α u))
  ∎

lifteval : ∀{Γ Δ σ τ}(α : Sub Γ Δ)(β : Env Δ)(v : Val σ)(y : Var (Γ < σ) τ) → ((eval β ∘ α) << v) y ≅ (eval (β << v) ∘ lift α) y
lifteval α β v zero = proof v ≡⟨⟩ v ∎
lifteval α β v (suc y) = 
  proof
  eval β (α y) 
  ≅⟨ reneval suc (β << v) (α y) ⟩
  eval (β << v) (ren suc (α y))
  ∎



subeval : ∀{Γ Δ σ}(α : Sub Γ Δ)(β : Env Δ)(t : Tm Γ σ) → eval (eval β ∘ α) t ≅ (eval β ∘ sub α) t
subeval α β tr = refl
subeval α β fls = refl
subeval α β (ifthenelse t u v) = cong₃ if_then_else_ (subeval α β t) (subeval α β u) (subeval α β v)
subeval α β zero = refl
subeval α β (suc n) = cong ℕ.suc (subeval α β n)
subeval α β (rec z f n) = cong₃ fold (subeval α β z) (subeval α β f) (subeval α β n)
subeval α β (tm ,, tm₁) = cong₂ _,_ (subeval α β tm) (subeval α β tm₁)
subeval α β (fst tm) = cong proj₁ (subeval α β tm)
subeval α β (snd tm) = cong proj₂ (subeval α β tm)
subeval {Γ} {Δ} α β (case {σ}{τ}{ρ} tm tm₁ tm₂) = 
  proof
  [_,_] {C = λ _ → Val ρ} (eval (λ x → eval β (α x)) tm) (eval (λ x → eval β (α x)) tm₁) (eval (λ x → eval β (α x)) tm₂)
  ≅⟨ cong₂ _$_ (cong₂ ([_,_] {C = λ _ → Val ρ}) (subeval {Γ} {Δ} α β tm) (subeval {Γ} {Δ} α β tm₁)) (subeval {Γ} {Δ} α β tm₂) ⟩
  [_,_] {C = λ _ → Val ρ} (eval β (sub α tm)) (eval β (sub α tm₁)) (eval β (sub α tm₂))
  ∎

subeval α β (left tm) = cong inj₁ (subeval α β tm)
subeval α β (right tm) = cong inj₂ (subeval α β tm)
subeval α β (var x) = proof eval β (α x) ≡⟨⟩ eval β (α x) ∎
subeval α β (lam t) = ext λ v → 
  proof
  eval ((eval β ∘ α) << v) t 
  ≅⟨ cong (λ (γ : Env _) → eval γ t) (iext λ σ → ext (lifteval α β v)) ⟩
  eval (eval (β << v) ∘ lift α) t
  ≅⟨ subeval (lift α) (β << v) t ⟩
  eval (β << v) (sub (lift α) t)
  ∎
subeval α β (app t u) = 
  proof
  eval (eval β ∘ α) t (eval (eval β ∘ α) u)
  ≅⟨ cong₂ _$_ (subeval α β t) (subeval α β u) ⟩
  eval β (sub α t) (eval β (sub α u))
  ∎


