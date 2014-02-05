{-# OPTIONS --type-in-type #-}

module CategoricalProperties where

open import Relation.Binary.HeterogeneousEquality
open import Function

open import Syntax
open import CategoryTheory
open import Evaluator


RenCat : Cat
RenCat = record {Obj  = Con;
                 Hom  = Ren;
                 iden = renId;
                 comp = renComp;
                 idl  = iext (λ _ → refl);
                 idr  = iext (λ _ → refl);
                 ass  = iext (λ _ → refl)}

SubCat : Cat
SubCat = record {Obj  = Con;
                 Hom  = Sub;
                 iden = subId;
                 comp = subComp;
                 idl  = λ {_ _ f} → iext (λ σ → ext (λ x → subid (f x)));
                 idr  = refl;
                 ass  = λ {_ _ _ _ f g h} → iext (λ σ → ext (subcomp f g ∘ h))}


VarF : Fun RenCat (Fam Ty)
VarF = record {
  OMap = Var;
  HMap = id;
  fid = refl;
  fcomp = refl}


TmRMonad : RMonad VarF
TmRMonad = record {
  T = Tm;
  η = var;
  bind = sub;
  law1 = iext (λ σ → ext subid);
  law2 = refl;
  law3 = λ {_ _ _ f g} → iext (λ σ → ext (subcomp g f))}



modelRAlg : Con → RAlg TmRMonad
modelRAlg Γ = record {
  acar = Val Γ;
  astr = λ {Γ} → λ γ → eval γ;
  alaw1 = refl;
  alaw2 = λ {Γ Δ α γ} → iext (λ σ → ext (subeval α γ))}

