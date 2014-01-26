module ReifyReflect where

open import Syntax
open import Data.Nat hiding (_<_)
open import Data.Product
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)

mutual 
  Val : Con → Ty → Set
  Val Γ ι       = Nf Γ ι
  Val Γ nat     = Nf Γ nat
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) 
                  λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval {σ = τ} ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval {σ = σ} ρ' v)

  renval : ∀{Γ Δ σ} → Ren Γ Δ → Val Γ σ → Val Δ σ
  renval {Γ} {Δ} {ι} α v   = renNf α v
  renval {Γ} {Δ} {nat} α v = renNf α v
  renval {Γ} {Δ} {σ ⇒ τ} α v = (λ {E} β v' → proj₁ v (renComp β α) v') , 
         (λ {Δ₁ Δ' : Con} (ρ : Ren Δ Δ₁) (ρ' : Ren Δ₁ Δ') (v₁ : Val Δ₁ σ) → 
           proof
           renval {σ = τ} ρ' (proj₁ v (λ {σ} x → ρ (α x)) v₁) 
           ≅⟨ proj₂ v {Δ₁} {Δ'} (renComp ρ α) ρ' v₁ ⟩
           proj₁ v (λ {σ} x → ρ' (ρ (α x))) (renval {σ = σ} ρ' v₁)
           ∎)


Σeq : {A : Set} {A' : Set} {B : A → Set} {B' : A' → Set} → {a : A} → {a' : A'} → a ≅ a' → B ≅ B' → {b : B a} → {b' : B' a'} → b ≅ b' → _,_ {B = B} a b ≅ _,_ {B = B'} a' b'
Σeq refl refl refl = refl

ir : ∀{A A' : Set} → {a : A} → {a' : A'} → {p q : a ≅ a'} → p ≅ q
ir {p = refl} {q = refl} = refl

fixedtypes : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a'' → p ≅ q
fixedtypes {p = refl} {q = refl} refl = refl

fixedtypesleft : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a ≅ a'' → p ≅ q
fixedtypesleft {p = refl} {q = refl} refl = refl

fixedtypesright : ∀{A A' A'' A''' : Set}{a : A}{a' : A'}{a'' : A''}{a''' : A'''} → {p : a ≅ a'} → {q : a'' ≅ a'''} → a' ≅ a''' → p ≅ q
fixedtypesright {p = refl} {q = refl} refl = refl


renvalcomp : ∀{Γ Δ E σ} → (ρ : Ren Γ Δ) → (ρ' : Ren Δ E) → (v : Val Γ σ) → renval {σ = σ} ρ' (renval {σ = σ} ρ v) ≅ renval {σ = σ} (ρ' ∘ ρ) v 
renvalcomp {Γ} {Δ} {E} {ι} ρ ρ' v = rennfcomp ρ' ρ v
renvalcomp {Γ} {Δ} {E} {nat} ρ ρ' v = rennfcomp ρ' ρ v
renvalcomp {Γ} {Δ} {E} {σ ⇒ σ₁} ρ ρ' (f , p) = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)



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


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → 
         (renval {σ = τ} ρ ∘ (γ << v)) x ≅ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << renval {σ = σ} ρ v) x
renval<< ρ γ v zero = refl
renval<< ρ γ v (suc x) = refl

ifcong : {A : Set}{B : A → Set}{f f' : {a : A} → B a} → _≅_ {_}{ {a : A} → B a } f { {a : A} → B a } f' → (a : A) → f {a} ≅ f' {a}
ifcong refl a = refl

fcong : ∀{A B : Set} → {f f' : A → B} → f ≅ f' → (a : A) → f a ≅ f' a
fcong refl a = refl

mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι   v = v
  reify nat v = v
  reify (σ ⇒ τ) v = nlam (reify τ (proj₁ v suc (reflect σ (nvar zero))))
  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι   n = ne n
  reflect nat n = ne n
  reflect (σ ⇒ τ) n = (λ α v → reflect τ (napp (renNe α n) (reify σ v))) , (λ ρ ρ' v → 
    proof
    renval {σ = τ} ρ' (reflect τ (napp (renNe ρ n) (reify σ v)))
    ≅⟨ renvalReflect {σ = τ} ρ' (napp (renNe ρ n) (reify σ v)) ⟩
    reflect τ (renNe ρ' (napp (renNe ρ n) (reify σ v)))
    ≅⟨ cong (reflect τ) refl ⟩
    reflect τ (napp (renNe ρ' (renNe ρ n)) (renNf ρ' (reify σ v)))
    ≅⟨ cong (reflect τ) (cong₂ napp (rennecomp ρ' ρ n) (reifyRenval ρ' v)) ⟩
    reflect τ (napp (renNe (ρ' ∘ ρ) n) (reify σ (renval {σ = σ} ρ' v)))
    ∎)
  
  renvalReflect : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Ne Γ σ) → renval {σ = σ} ρ (reflect σ n) ≅ reflect σ (renNe ρ n)
  renvalReflect {Γ} {Δ} {ι} ρ n = refl
  renvalReflect {Γ} {Δ} {nat} ρ n = refl
  renvalReflect {Γ} {Δ} {σ ⇒ τ} ρ n = Σeq 
    (iext λ _ → ext λ (α : Ren _ _) → ext λ v → proof
      reflect τ (napp (renNe (α ∘ ρ) n) (reify σ v))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp α ρ n)) refl) ⟩ 
      reflect τ (napp (renNe α (renNe ρ n)) (reify σ v))
      ∎) 
    refl
    ((iext λ _ → iext λ _ → ext λ (ρ₁ : Ren _ _) → ext λ (ρ' : Ren _ _) → ext λ v₁ → fixedtypes (proof
      reflect τ (napp (renNe (ρ' ∘ ρ₁ ∘ ρ) n) (reify σ (renval {σ = σ} ρ' v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp (sym (rennecomp ρ' (ρ₁ ∘ ρ) n)) (sym (reifyRenval ρ' v₁))) ⟩
      reflect τ (napp (renNe ρ' (renNe (ρ₁ ∘ ρ) n)) (renNf ρ' (reify σ v₁)))
      ≅⟨ cong (reflect τ) (cong₂ napp refl refl) ⟩
      reflect τ (renNe ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ sym (renvalReflect ρ' (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁))) ⟩
      renval {σ = τ} ρ' (reflect τ (napp (renNe (ρ₁ ∘ ρ) n) (reify σ v₁)))
      ≅⟨ cong ( λ f → renval {σ = τ} ρ' (reflect τ (napp f (reify σ v₁)))) (sym (rennecomp ρ₁ ρ n)) ⟩
      renval {σ = τ} ρ' (reflect τ (napp (renNe ρ₁ (renNe ρ n)) (reify σ v₁)))
      ∎)))

  reifyRenval : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Val Γ σ) → renNf ρ (reify σ n) ≅ reify σ (renval {σ = σ} ρ n)
  reifyRenval {Γ} {Δ} {ι}   ρ n = proof renNf ρ n ≡⟨⟩ renNf ρ n ∎
  reifyRenval {Γ} {Δ} {nat} ρ n = proof renNf ρ n ≡⟨⟩ renNf ρ n ∎
  reifyRenval {Γ} {Δ} {σ ⇒ τ} ρ n = proof
    nlam (renNf (wk ρ) (reify τ (proj₁ n suc (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (reifyRenval (wk ρ) (proj₁ n suc (reflect σ (nvar zero)))) ⟩
    nlam (reify τ (renval {σ = τ} (wk ρ) (proj₁ n suc (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (cong (reify τ) (proj₂ n suc (wk ρ) (reflect σ (nvar zero)))) ⟩
    nlam (reify τ (proj₁ n ((wk ρ) ∘ suc) (renval {σ = σ} (wk ρ) (reflect σ (nvar zero)))))
    ≅⟨ cong nlam (cong (reify τ) (cong₂ (proj₁ n) refl (renvalReflect {σ = σ} (wk ρ) (nvar zero)))) ⟩
    nlam (reify τ (proj₁ n (suc ∘ ρ) (reflect σ (nvar zero))))
    ∎



nfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
nfold {σ = σ} z f (ne x) = reflect σ (nrec (reify _ z) (reify _ f) x)
nfold z f nzero = z
nfold {σ = σ} z f (nsuc n) = proj₁ f renId (nfold {σ = σ} z f n)

renvalnfold : ∀{Γ Δ σ} (ρ : Ren Γ Δ)(z : Val Γ σ)(f : Val Γ (σ ⇒ σ))(n : Val Γ nat) → renval {σ = σ} ρ (nfold {σ = σ} z f n) ≅ 
              nfold {σ = σ} (renval {σ = σ} ρ z) (renval {σ = σ ⇒ σ} ρ f) (renval {σ = nat} ρ n)
renvalnfold {_}{_}{σ} ρ z f (ne x) = proof
  renval {σ = σ} ρ (reflect σ (nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x))
  ≅⟨ renvalReflect ρ ((nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x)) ⟩
  reflect σ (renNe ρ (nrec (reify σ z) (nlam (reify σ (proj₁ f suc (reflect σ (nvar zero))))) x))
  ≅⟨ cong (reflect σ) (cong₃ nrec 
    (reifyRenval ρ z) 
    (cong nlam (proof
          renNf (wk ρ) (reify σ (proj₁ f suc (reflect σ (nvar zero))))
          ≅⟨ reifyRenval (wk ρ) (proj₁ f suc (reflect σ (nvar zero))) ⟩
          reify σ (renval {σ = σ} (wk ρ) (proj₁ f suc (reflect σ (nvar zero))))
          ≅⟨ cong (reify σ) (proj₂ f suc (wk ρ) (reflect σ (nvar zero))) ⟩
          reify σ (proj₁ f ((wk ρ) ∘ suc) (renval {σ = σ} (wk ρ) (reflect σ (nvar zero))))
          ≅⟨ cong (reify σ) (cong₂ (proj₁ f) refl (renvalReflect {σ = σ} (wk ρ) (nvar zero))) ⟩
          reify σ (proj₁ f (suc ∘ ρ) (reflect σ (nvar zero)))
          ∎)) 
    (proof renNe ρ x ≡⟨⟩ renNe ρ x ∎)) ⟩
  reflect σ (nrec (reify σ (renval {σ = σ} ρ z)) (nlam (reify σ (proj₁ f (suc ∘ ρ) (reflect σ (nvar zero))))) (renNe ρ x))
  ∎
renvalnfold {σ = σ} ρ z f nzero = proof renval {σ = σ} ρ z ≡⟨⟩ renval {σ = σ} ρ z ∎
renvalnfold {σ = σ} ρ z f (nsuc n) = proof
  renval {σ = σ} ρ (proj₁ f renId (nfold {σ = σ} z f n)) 
  ≅⟨ proj₂ f renId ρ (nfold {σ = σ} z f n) ⟩
  proj₁ f ρ (renval {σ = σ} ρ (nfold {σ = σ} z f n))
  ≅⟨ cong (proj₁ f ρ) (renvalnfold {σ = σ} ρ z f n) ⟩
  proj₁ f ρ (nfold {σ = σ} (renval {σ = σ} ρ z) ((λ β → proj₁ f (β ∘ ρ)) , (λ ρ₁ ρ' v₁ → trans (proj₂ f (ρ₁ ∘ ρ) ρ' v₁) refl)) (renNf ρ n))
  ∎
