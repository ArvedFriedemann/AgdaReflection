module ReflectionSolver where

open import Util


record ComplExpr Expr where
  field
    unit : Expr
    _<>_ : Expr -> Expr -> Expr
    _~>_ : Expr -> Expr -> Expr
    _::_ : Expr -> Expr -> Expr
    _~=~_ : Expr -> Expr -> Expr

    step : Expr -> Expr













--
