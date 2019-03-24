-- | Implementation of the "hover" functionality, i.e. finding the type of the
--   symbol below the cursor.
module Backend.Dhall.Hover (
  typeAt
  ) where

import Dhall.Parser (Src(..))
import Dhall.Core (Expr(..), shift, normalize, Var(..))
import Dhall.Context (Context(..), insert)
import Dhall.TypeCheck (X, TypeError, typeWith)

import Text.Megaparsec.Pos (SourcePos)

-- X is the empty type
type Expr' = Expr Src X

-- assumption: every subexpression is wrapped in Note constructor.
left :: Expr' -> SourcePos
left (Note (Src l _ _) _) = l

right :: Expr' -> SourcePos
right (Note (Src _ r _) _) = r

posIn :: SourcePos -> Expr'  -> Bool
posIn src exp = left exp <= src && src < right exp

-- todo: give type of operator rather than of whole expression?
-- i.e. typeOf t -> typeOf u -> typeOf exp
                             
-- only need to handle expressions that contain sub-expressions
typeAt :: SourcePos -> Context Expr' -> Expr' -> Either (TypeError Src X) Expr'
typeAt src ctx exp = case exp of
  Note _ t -> typeAt src ctx t
  Lam x t u | src `posIn` t -> typeAt src ctx t  -- type of bound variable
            | src `posIn` u -> let ctx' = fmap (shift 1 (V x 0)) (insert x (normalize t) ctx)
                               in typeAt src ctx' u  -- body
            | src < left t -> typeWith ctx t  -- bound variable
            | otherwise -> typeWith ctx exp  -- the arrow between binder and body?
  Pi x t u | src `posIn` t -> typeAt src ctx t  -- type of bound variable
           | src `posIn` u -> let ctx' = fmap (shift 1 (V x 0)) (insert x (normalize t) ctx)
                               in typeAt src ctx' u  -- body
           | src < left t -> typeWith ctx t  -- bound variable
           | otherwise -> typeWith ctx exp  -- the arrow between binder and body?
  App t u | src `posIn` t -> typeAt src ctx t  -- function
          | src `posIn` u -> typeAt src ctx u  -- argument
  --Let ?
  Annot t u | src `posIn` t -> typeAt src ctx t  -- body
            | src `posIn` u -> typeAt src ctx u  -- type annotation
            | otherwise -> typeWith ctx exp  -- the colon in between?
  -- uninteresting cases, could be generalised into a single Expr constructor?
  BoolAnd t u -> binaryConstructor t u
  BoolOr t u -> binaryConstructor t u
  BoolEQ t u -> binaryConstructor t u
  BoolNE t u -> binaryConstructor t u
  NaturalPlus t u -> binaryConstructor t u
  NaturalTimes t u -> binaryConstructor t u
  TextAppend t u -> binaryConstructor t u
  ListAppend t u -> binaryConstructor t u
  Combine t u -> binaryConstructor t u
  CombineTypes t u -> binaryConstructor t u
  Prefer t u -> binaryConstructor t u
  ImportAlt t u -> binaryConstructor t u -- clarify semantics?
  
  -- unary
  Some t -> unaryConstructor t
  {-
  -- interesting cases TODO
  Field t
  Embed a
  ListLit
  OptionalLit
  Record
  RecorLit
  Union
  UnionLit
  Merge
  Project
  -}
  -- ternary
  BoolIf t u u' | src `posIn` t -> typeAt src ctx t
                | src `posIn` u -> typeAt src ctx u
                | src `posIn` u' -> typeAt src ctx u'
                | otherwise -> typeWith ctx exp
  -- catches any other constructor that does not contain subexpressions
  _ -> typeWith ctx exp
 where binaryConstructor :: Expr' -> Expr' -> Either (TypeError Src X) Expr'
       binaryConstructor t u | src `posIn` t = typeAt src ctx t
                             | src `posIn` u = typeAt src ctx u
                             | otherwise = typeWith ctx exp
                             
       unaryConstructor :: Expr' -> Either (TypeError Src X) Expr'
       unaryConstructor t | src `posIn` t = typeAt src ctx t
                          | otherwise = typeWith ctx exp

