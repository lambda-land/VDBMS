-- Brute force translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
module VDB.QueryTrans.RelAlg2Sql where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import VDB.Variational
import VDB.Config  
import VDB.VqueryConfigSem
import VDB.Variant

-- import Data.Text as T (Text, pack, append, concat)
import Data.List (intercalate)
import Data.Maybe (catMaybes)

type Query = String
type VariantQuery = Variant Query Bool

-- | takes a variational query and a list of configurations
--   and returns a list of relational sql queries tagged with
--   their configuration.
alg2Sql :: Algebra -> [Config Bool] -> [VariantQuery]
alg2Sql q cs = map (variantQ q) cs 
  where
    variantQ :: Algebra -> Config Bool -> VariantQuery
    variantQ cQ c = case relAlgTrans configuredQ of 
      Just relQ -> (relQ, c)
      _ -> error "configuring vquery went wrong!!"
      where configuredQ = configureVquery cQ c



-- | takes a vq and returns a "just text" if vq is a pure
--   relational query and returns "nothing" otherwise.
-- Note: it's used in brute force.
relAlgTrans :: Algebra -> Maybe Query
relAlgTrans (SetOp Prod l r) = case (l,r) of 
  (TRef l', TRef r') ->
  (AChc _ _ _, _) -> Nothing
  (_, AChc _ _ _) -> Nothing
  (Empty, _) ->
  (_, Empty) ->
  (TRef l', _) ->
  (_, TRef r') ->
  _ ->
relAlgTrans (SetOp o l r) = case (l,r) of
  (TRef l', TRef r') -> 
  (AChc _ _ _, _) -> Nothing
  (_, AChc _ _ _) -> Nothing
  (Empty, Empty) ->
  (TRef l', _) ->
  (_, TRef r') ->
  _ ->
  where 
    ot = if o == Union then " union " else " except "
relAlgTrans (Proj as q)   = case relPrj as of 
  Nothing -> Nothing
  Just [] -> error "syntactically incorrect q! cannot have an empty list of att!!"
  Just _ -> case q of 
    Proj as' q' ->
    Sel c q' ->
    SetOp Prod l r -> case (l,r) of
      (TRef l', TRef r') ->
      (AChc _ _ _, _) -> Nothing
      (_, AChc _ _ _) -> Nothing
      (Empty, _) ->
      (_, Empty) ->
      (TRef l', _) ->
      (_, TRef r') ->
      _ ->
    SetOp o l r -> case (l,r) of
      (TRef l', TRef r') ->
      (Empty, Empty) ->
      (AChc _ _ _, _) -> Nothing
      (_, AChc _ _ _) -> Nothing
      (TRef l', _) ->
      (_, TRef r') ->
      _ -> 
      where 
        ares = relPrjAux as
        ot = if o == Union then " union " else " except "
    AChc _ _ _ -> Nothing
    TRef r ->
    Empty -> 
    _ -> 
relAlgTrans (Sel c q)     = case q of 
  SetOp Prod l r -> case (l,r) of
    (TRef l', TRef r') ->
    (AChc _ _ _, _) -> Nothing
    (_, AChc _ _ _) -> Nothing
    (Empty, _) ->
    (_, Empty) ->
    (_, TRef r') ->
    (TRef l', _) ->
    _ ->
    where
      cres = relSelAux c
  SetOp o l r -> case (l,r) of
    (TRef l', TRef r') ->
    (Empty, Empty) ->
    (AChc _ _ _, _) -> Nothing
    (_, AChc _ _ _) -> Nothing
    (TRef l', _) ->
    (_, TRef r') ->
    _ ->
  where
    cres = relSelAux c
    ot = if o == Union then " union " else " except "
  Proj as q' ->
  Sel c' q' ->
  TRef r ->
  Empty ->
  AChc _ _ _ -> Nothing
  _ ->
relAlgTrans (AChc _ _ _)  = Nothing
relAlgTrans (TRef r)      = Just $ concat ["select * from ", relationName r]
relAlgTrans Empty         = Just "select null"

-- | helper function for projecting pure relational attributes.
relPrj :: [Opt Attribute] -> Maybe String
relPrj [] = Just []
relPrj as
  | Nothing `elem` (attListName as) = Nothing
  | otherwise                       = Just (intercalate ", " (catMaybes (attListName as)))

-- | helper function for relPrj.
-- attName :: Opt Attribute -> Maybe String
-- attName (F.Lit True, a) = Just (attributeName a)
-- attName _             = Nothing

-- | helper function for relPrj.
attListName :: [Opt Attribute] -> [Maybe String]
attListName = map attName 
  where 
    attName :: Opt Attribute -> Maybe String
    attName (F.Lit True, a) = Just (attributeName a)
    attName _               = Nothing


