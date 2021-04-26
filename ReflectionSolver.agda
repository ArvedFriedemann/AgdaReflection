module ReflectionSolver where

open import Util

data Type where
  set : Type
  pi : Type -> (Type -> Type) -> Type
  sigma : Type -> (Type -> Type) -> Type

  _xXx_ : Type -> Type -> Type
  _+++_ : Type -> Type -> Type

-- TODO: concrete proof constructors
data Proof (P : Type) (T : Type) : Set where
  pi-proof : (T === pi A B) ->
              Proof a A -> Proof b (B a) -> Proof P T
  sigma-proof : (T === sigma A B) ->
              Proof a A -> Proof b (B a) -> Proof P (A xXx (B a)) -> Proof P T
  prod-proof-l : (T === A xXx B) ->
              Proof a A -> Proof b B -> Proof P T
  coprop-proof-l : (T === A +++ B) ->
              Proof a A -> Proof P T
  coprop-proof-r : (T === A +++ B) ->
              Proof b B -> Proof P T

mkProof : (T : Type) -> Maybe (exists (P : Type) st Proof P T)
mkProof = {!!}

record ComplExpr Expr where
  field
    unit : Expr
    _<>_ : Expr -> Expr -> Expr
    _~>_ : Expr -> Expr -> Expr
    _::_ : Expr -> Expr -> Expr
    _~=~_ : Expr -> Expr -> Expr

    step : Expr -> Expr














--
