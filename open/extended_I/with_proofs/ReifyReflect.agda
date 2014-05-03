module ReifyReflect where

open import Syntax
open import Data.Nat hiding (_<_)
open import Data.Product hiding (map)
--open import Data.List hiding ([_])
--open import Data.List.Properties
--open import Data.Sum hiding (map)
open import Function
open import Relation.Binary.HeterogeneousEquality
open ≅-Reasoning renaming (begin_ to proof_)

data ListVal (A B : Set) : Set where
  neLV   : B → ListVal A B
  nilLV  : ListVal A B
  consLV : A → ListVal A B → ListVal A B

mapLV : ∀{A B C D} → (A → C) → (B → D) → ListVal A B → ListVal C D
mapLV f g (neLV x)      = neLV (g x)
mapLV f g nilLV         = nilLV
mapLV f g (consLV x xs) = consLV (f x) (mapLV f g xs)


mutual 
  Val : Con → Ty → Set
  Val Γ ι       = Nf Γ ι
  Val Γ nat     = Nf Γ nat
  Val Γ (σ ⇒ τ) = Σ (∀{Δ} → Ren Γ Δ → Val Δ σ → Val Δ τ) 
                λ f → ∀{Δ Δ'}(ρ : Ren Γ Δ)(ρ' : Ren Δ Δ')(v : Val Δ σ) → renval {σ = τ} ρ' (f ρ v) ≅ f (ρ' ∘ ρ) (renval {σ = σ} ρ' v)
  Val Γ [ σ ]   = ListVal (Val Γ σ) (Ne Γ [ σ ])

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
  renval {Γ} {Δ} {[ σ ]} α v = mapLV (renval {σ = σ} α) (renNe α) v


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


renvalcomp : ∀{Γ Δ E σ} → (ρ' : Ren Δ E) → (ρ : Ren Γ Δ) → (v : Val Γ σ) → renval {σ = σ} ρ' (renval {σ = σ} ρ v) ≅ renval {σ = σ} (ρ' ∘ ρ) v 
renvalcomp {σ = ι} ρ' ρ v = rennfcomp ρ' ρ v
renvalcomp {σ = nat} ρ' ρ v = rennfcomp ρ' ρ v
renvalcomp {σ = σ ⇒ τ} ρ' ρ v = Σeq refl refl (iext λ Δ₁ → iext λ Δ' → ext λ ρ₁ → ext λ ρ'' → ext λ v₁ → ir)
renvalcomp {σ = [ σ ]} ρ' ρ (neLV x) = cong neLV (rennecomp ρ' ρ x)
renvalcomp {σ = [ σ ]} ρ' ρ nilLV = refl
renvalcomp {Γ}{Δ}{E}{σ = [ σ ]} ρ' ρ (consLV x v) = cong₂ consLV (renvalcomp {σ = σ} ρ' ρ x) (renvalcomp {σ = [ σ ]} ρ' ρ v)



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


renval<< : ∀{Γ Δ E σ} → (ρ : Ren Δ E) → (γ : Env Γ Δ) → (v : Val Δ σ) → ∀{τ}(x : Var (Γ < σ) τ) → 
         (renval {σ = τ} ρ ∘ (γ << v)) x ≅ ((λ {σ'} → renval {σ = σ'} ρ ∘ γ) << renval {σ = σ} ρ v) x
renval<< ρ γ v vze = refl
renval<< ρ γ v (vsu x) = refl

ifcong : {A : Set}{B : A → Set}{f f' : {a : A} → B a} → _≅_ {_}{ {a : A} → B a } f { {a : A} → B a } f' → (a : A) → f {a} ≅ f' {a}
ifcong refl a = refl

fcong : ∀{A B : Set} → {f f' : A → B} → f ≅ f' → (a : A) → f a ≅ f' a
fcong refl a = refl


mutual
  reify : ∀{Γ} σ → Val Γ σ → Nf Γ σ
  reify ι   v = v
  reify nat v = v
  reify (σ ⇒ τ) v = nlam (reify τ (proj₁ v vsu (reflect σ (nvar vze))))
  reify [ σ ] (neLV x) = ne[] x
  reify [ σ ] nilLV = nnil
  reify [ σ ] (consLV x xs) = ncons (reify _ x) (reify _ xs)

  
  reflect : ∀{Γ} σ → Ne Γ σ → Val Γ σ
  reflect ι   n = ne n
  reflect nat n = nenat n
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
  reflect [ σ ] n = neLV n

  renvalReflect : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Ne Γ σ) → renval {σ = σ} ρ (reflect σ n) ≅ reflect σ (renNe ρ n)
  renvalReflect {Γ} {Δ} {ι} ρ n = refl
  renvalReflect {Γ} {Δ} {nat} ρ n = cong nenat refl
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
  renvalReflect {Γ} {Δ} {[ σ ]} ρ l = proof neLV (renNe ρ l) ≡⟨⟩ neLV (renNe ρ l) ∎

  reifyRenval : ∀{Γ Δ σ}(ρ : Ren Γ Δ)(n : Val Γ σ) → renNf ρ (reify σ n) ≅ reify σ (renval {σ = σ} ρ n)
  reifyRenval {Γ} {Δ} {ι}   ρ n = proof renNf ρ n ≡⟨⟩ renNf ρ n ∎
  reifyRenval {σ = nat} ρ v = refl
  reifyRenval {Γ} {Δ} {σ ⇒ τ} ρ n = proof
    nlam (renNf (wk ρ) (reify τ (proj₁ n vsu (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (reifyRenval (wk ρ) (proj₁ n vsu (reflect σ (nvar vze)))) ⟩
    nlam (reify τ (renval {σ = τ} (wk ρ) (proj₁ n vsu (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (cong (reify τ) (proj₂ n vsu (wk ρ) (reflect σ (nvar vze)))) ⟩
    nlam (reify τ (proj₁ n ((wk ρ) ∘ vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze)))))
    ≅⟨ cong nlam (cong (reify τ) (cong₂ (proj₁ n) refl (renvalReflect {σ = σ} (wk ρ) (nvar vze)))) ⟩
    nlam (reify τ (proj₁ n (vsu ∘ ρ) (reflect σ (nvar vze))))
    ∎
  reifyRenval {σ = [ σ ]} ρ (neLV x) = proof ne[] (renNe ρ x) ≡⟨⟩ ne[] (renNe ρ x) ∎
  reifyRenval {σ = [ σ ]} ρ nilLV = refl
  reifyRenval {σ = [ σ ]} ρ (consLV x xs) = cong₂ ncons (reifyRenval {σ = σ} ρ x) (reifyRenval {σ = [ σ ]} ρ xs) 



natfold : ∀{Γ σ} → Val Γ σ  → Val Γ (σ ⇒ σ) → Val Γ nat → Val Γ σ
natfold {σ = σ} z f (nenat x) = reflect σ (nrec (reify _ z) (reify _ f) x)
natfold z f nze = z
natfold {σ = σ} z f (nsu n) = proj₁ f renId (natfold {σ = σ} z f n)


listfold : ∀{Γ σ τ} → Val Γ τ → Val Γ (σ ⇒ τ ⇒ τ) → Val Γ [ σ ] → Val Γ τ
listfold {σ = σ}{τ = τ} z f (neLV x) = reflect τ (nfold {σ = σ}{τ = τ} (reify _ z) (reify _ f) x)
listfold z f nilLV = z
listfold {τ = τ} z f (consLV x xs) = proj₁ (proj₁ f renId x) renId (listfold {τ = τ} z f xs)


renvalnatfold : ∀{Γ Δ σ} (ρ : Ren Γ Δ)(z : Val Γ σ)(f : Val Γ (σ ⇒ σ))(n : Val Γ nat) → renval {σ = σ} ρ (natfold {σ = σ} z f n) ≅ 
              natfold {σ = σ} (renval {σ = σ} ρ z) (renval {σ = σ ⇒ σ} ρ f) (renval {σ = nat} ρ n)
renvalnatfold {σ = σ}ρ z f (nenat x) = proof
  renval {σ = σ} ρ (reflect σ (nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x))
  ≅⟨ renvalReflect ρ ((nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x)) ⟩
  reflect σ (renNe ρ (nrec (reify σ z) (nlam (reify σ (proj₁ f vsu (reflect σ (nvar vze))))) x))
  ≅⟨ cong (reflect σ) (cong₃ nrec 
    (reifyRenval ρ z) 
    (cong nlam (proof
          renNf (wk ρ) (reify σ (proj₁ f vsu (reflect σ (nvar vze))))
          ≅⟨ reifyRenval (wk ρ) (proj₁ f vsu (reflect σ (nvar vze))) ⟩
          reify σ (renval {σ = σ} (wk ρ) (proj₁ f vsu (reflect σ (nvar vze))))
          ≅⟨ cong (reify σ) (proj₂ f vsu (wk ρ) (reflect σ (nvar vze))) ⟩
          reify σ (proj₁ f ((wk ρ) ∘ vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze))))
          ≅⟨ cong (reify σ) (cong₂ (proj₁ f) refl (renvalReflect {σ = σ} (wk ρ) (nvar vze))) ⟩
          reify σ (proj₁ f (vsu ∘ ρ) (reflect σ (nvar vze)))
          ∎)) 
    (proof renNe ρ x ≡⟨⟩ renNe ρ x ∎)) ⟩
  reflect σ (nrec (reify σ (renval {σ = σ} ρ z)) (nlam (reify σ (proj₁ f (vsu ∘ ρ) (reflect σ (nvar vze))))) (renNe ρ x))
  ∎
renvalnatfold {σ = σ} ρ z f nze = proof renval {σ = σ} ρ z ≡⟨⟩ renval {σ = σ} ρ z ∎
renvalnatfold {σ = σ} ρ z f (nsu n) = proof
  renval {σ = σ} ρ (proj₁ f renId (natfold {σ = σ} z f n)) 
  ≅⟨ proj₂ f renId ρ (natfold {σ = σ} z f n) ⟩
  proj₁ f ρ (renval {σ = σ} ρ (natfold {σ = σ} z f n))
  ≅⟨ cong (proj₁ f ρ) (renvalnatfold {σ = σ} ρ z f n) ⟩
  proj₁ f ρ (natfold {σ = σ} (renval {σ = σ} ρ z) ((λ β → proj₁ f (β ∘ ρ)) , (λ ρ₁ ρ' v₁ → trans (proj₂ f (ρ₁ ∘ ρ) ρ' v₁) refl)) (renNf ρ n))
  ∎


renvalinner : ∀{Γ Δ σ τ} → (f : Val Γ (σ ⇒ τ ⇒ τ))(α : Ren Γ Δ)(x : Val Γ σ)(y : Val Δ τ) → 
            proj₁ (proj₁ f renId x) α y ≅ proj₁ (proj₁ f α (renval {σ = σ} α x)) renId y
renvalinner {Γ}{Δ}{σ = σ}{τ = τ} f α x y = proof
  proj₁ (proj₁ f renId x) α y 
  ≡⟨⟩
  proj₁ (renval {σ = τ ⇒ τ} α (proj₁ f renId x)) renId y
  ≅⟨ cong (λ (f : Val Δ (τ ⇒ τ)) → proj₁ f renId y) (proj₂ f renId α x) ⟩
  proj₁ (proj₁ f α (renval {σ = σ} α x)) renId y
  ∎ 


renvallistfold : ∀{Γ Δ σ τ} (ρ : Ren Γ Δ)(z : Val Γ τ)(f : Val Γ (σ ⇒ τ ⇒ τ))(n : Val Γ [ σ ]) → renval {σ = τ} ρ (listfold {τ = τ} z f n) ≅ 
              listfold {τ = τ} (renval {σ = τ} ρ z) (renval {σ = σ ⇒ τ ⇒ τ} ρ f) (renval {σ = [ σ ]} ρ n)
renvallistfold {σ = σ}{τ = τ} ρ z f (neLV x) = proof
  renval {σ = τ} ρ (reflect τ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))))) x))
  ≅⟨ renvalReflect ρ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))))) x) ⟩
  reflect τ (renNe ρ (nfold (reify τ z) (nlam (nlam (reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))))) x))
  ≅⟨ cong (reflect τ) 
     (cong₃ nfold 
       (reifyRenval ρ z) --reify τ (proj₁ (renval {σ = τ ⇒ τ} (wk ρ) (proj₁ f vsu (reflect σ (nvar vze)))) vsu (reflect τ (nvar vze)))
       (cong (λ x → nlam (nlam x)) (proof
         renNf (wk (wk ρ)) (reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze))))
         ≅⟨ reifyRenval (wk (wk ρ)) (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze))) ⟩
         reify τ (renval {σ = τ} (wk (wk ρ)) (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) vsu (reflect τ (nvar vze))))
         ≅⟨ cong (reify τ) (proj₂ (proj₁ f vsu (reflect σ (nvar vze))) vsu (wk (wk ρ)) (reflect τ (nvar vze)) ) ⟩
         reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) (renComp vsu (wk ρ)) (renval {σ = τ} (wk (wk ρ)) (reflect τ (nvar vze))))
         ≅⟨ cong (λ x → reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) (renComp vsu (wk ρ)) x)) (renvalReflect (wk (wk ρ)) (nvar vze)) ⟩
         reify τ (proj₁ (proj₁ f vsu (reflect σ (nvar vze))) (renComp vsu (wk ρ)) (reflect τ (nvar vze)))
         ≡⟨⟩
         reify τ (proj₁ (renval {σ = τ ⇒ τ} (wk ρ) (proj₁ f vsu (reflect σ (nvar vze)))) vsu (reflect τ (nvar vze)))
         ≅⟨ cong (λ (f : Val _ (τ ⇒ τ)) → reify τ (proj₁ f vsu (reflect τ (nvar vze)))) (proj₂ f vsu (wk ρ) (reflect σ (nvar vze))) ⟩
         reify τ (proj₁ (proj₁ f (renComp (wk ρ) vsu) (renval {σ = σ} (wk ρ) (reflect σ (nvar vze)))) vsu (reflect τ (nvar vze)))
         ≅⟨ cong (λ x → reify τ (proj₁ (proj₁ f (renComp (wk ρ) vsu) x) vsu (reflect τ (nvar vze)))) (renvalReflect (wk ρ) (nvar vze)) ⟩
         reify τ (proj₁ (proj₁ f (renComp (wk ρ) vsu) (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))
         ≡⟨⟩
         reify τ (proj₁ (proj₁ f (renComp vsu ρ) (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))
         ∎)) 
       refl) ⟩
  reflect τ (nfold (reify τ (renval {σ = τ} ρ z)) (nlam (nlam (reify τ (proj₁ (proj₁ f (renComp vsu ρ) (reflect σ (nvar vze))) vsu (reflect τ (nvar vze)))))) (renNe ρ x))
  ∎
renvallistfold ρ z f nilLV = refl
renvallistfold {σ = σ}{τ = τ} ρ z f (consLV x xs) = proof
  renval {σ = τ} ρ (proj₁ (proj₁ f renId x) renId (listfold {τ = τ} z f xs)) 
  ≅⟨ proj₂ (proj₁ f renId x) renId ρ (listfold {τ = τ} z f xs) ⟩ 
  proj₁ (proj₁ f renId x) ρ (renval {σ = τ} ρ (listfold {τ = τ} z f xs))
  ≅⟨ cong (proj₁ (proj₁ f renId x) ρ) (renvallistfold {σ = σ}{τ = τ} ρ z f xs) ⟩
  proj₁ (proj₁ f renId x) ρ (listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) ,
       (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))
  ≅⟨ renvalinner {σ = σ}{τ = τ} f ρ x ((listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) ,
       (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))) ⟩
  proj₁ (proj₁ f (renComp renId ρ) (renval {σ = σ} ρ x)) renId 
    (listfold {τ = τ} (renval {σ = τ} ρ z) ((λ {E} β → proj₁ f (renComp β ρ)) , 
    (λ {Δ₁} {Δ'} ρ₁ ρ' v₁ → trans (proj₂ f (renComp ρ₁ ρ) ρ' v₁) refl)) (mapLV (renval {σ = σ} ρ) (renNe ρ) xs))
  ∎

