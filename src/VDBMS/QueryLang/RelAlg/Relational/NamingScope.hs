-- | it names every subquery if it's not renamed already
  -- and adjusts the qualifier of attirubtes both in 
  -- projection and conditions. note that if conditions
  -- don't have qualifiers it won't add them because
  -- they won't matter since the input query is type-correct.
module VDBMS.QueryLang.RelAlg.Relational.NamingScope where


import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name

import Control.Monad.State

-- import qualified Data.Map as M 
import qualified Data.Map.Strict as SM

import Data.Maybe (fromJust, isNothing)

type AliasNum = Int 

type RenameEnv = SM.Map Relation Name 

data StateInfo = StateInfo 
  { counter :: AliasNum
  , env :: RenameEnv
  }

incCounter :: StateInfo -> StateInfo
incCounter (StateInfo c e) = StateInfo (c+1) e

addR2env :: Relation -> StateInfo -> StateInfo
addR2env r (StateInfo c e) = StateInfo (c+1) (SM.insert r ("t" ++ show c) e)

type QState = State StateInfo

-- | evaluate the qstate with zero.
evalQState :: QState a -> a 
evalQState = flip evalState initState
  where initState = StateInfo 0 SM.empty

-- | gives name to subqueries in a relational algebra query.
nameSubqRAlgebra :: RAlgebra -> RAlgebra
nameSubqRAlgebra q = 
  case q' of 
      (RRenameAlg _ q'') -> q''
      _ -> q'
    where
      q' = evalQState (nameSubqRA q)

-- |
nameSubqRA :: RAlgebra -> QState RAlgebra
nameSubqRA (RSetOp o l r)   = 
  do l' <- nameSubqRA l 
     r' <- nameSubqRA r 
     modify incCounter
     sc <- gets counter
     -- se <- gets env
     let q' = RRenameAlg ("t" ++ show sc) (RSetOp o l' r')
     return q'
nameSubqRA (RProj as q)     = 
  do q' <- nameSubqRA q 
     -- s <- get
     modify incCounter
     sc <- gets counter
     se <- gets env
     let as' = updateAttsQual as q se 
         q'' = RRenameAlg ("t" ++ show sc) (RProj as' q')
     return q''
nameSubqRA (RSel c q)       = 
  do q' <- nameSubqRA q 
     se <- gets env
     let c'  = updateCond c q se
         q'' = RSel c' q'
     return q''
nameSubqRA (RJoin l r c)    = 
  do l' <- nameSubqRA l
     r' <- nameSubqRA r 
     se <- gets env
     let c'  = updateJoinCond c l' r' se 
         q'' = RJoin l' r' c' 
     return q''
nameSubqRA (RProd l r)      = 
  do l' <- nameSubqRA l
     r' <- nameSubqRA r
     return $ RProd l' r'
nameSubqRA q@(RTRef r)      = 
  do sc <- gets counter
     modify (addR2env r)
     return $ RRenameAlg ("t" ++ show sc) q
nameSubqRA q@(RRenameAlg _ _) = 
  do 
     -- q' <- nameSubqRA q
     return q
nameSubqRA REmpty           = 
  return REmpty

-- -- | update att qual for attributes. 
updateAttsQual :: Attributes -> RAlgebra -> RenameEnv -> Attributes
updateAttsQual as q e = 
  map (flip (flip updateAttQual q) e) as

-- | updates the attribute qualifier if it has one. from the 
--   old query q to the new query q'. 
-- TODO: i may need to get the most outermost name instead of lookup
updateAttQual :: Attr -> RAlgebra -> RenameEnv -> Attr
updateAttQual a _ e 
  | isQualRel aq = 
    updateAttrQual 
      a 
      (SubqueryQualifier (fromJust (SM.lookup (relQualifier aq) e)))
  | otherwise    = a
    where
      aq = fromJust (qualifier a) 


-- | updates the existing qualifier of attributes in a condition. 
updateCond :: SqlCond RAlgebra -> RAlgebra -> RenameEnv -> SqlCond RAlgebra
updateCond (SqlCond c)   q e = SqlCond $ updateRCond c q e
updateCond c@(SqlIn _ _) _ _ = c
updateCond (SqlNot c)    q e = SqlNot c'
  where
    c' = updateCond c q e
updateCond (SqlOr l r)   q e = SqlOr l' r'
  where
    l' = updateCond l q e
    r' = updateCond r q e
updateCond (SqlAnd l r)  q e = SqlAnd l' r' 
  where
    l' = updateCond l q e
    r' = updateCond r q e

-- |
updateRCond :: RCondition -> RAlgebra -> RenameEnv -> RCondition
updateRCond c@(RLit _)    _ _  = c
updateRCond (RComp o l r) q e = RComp o l' r' 
  where 
    l' = updateAtom l q e
    r' = updateAtom r q e
updateRCond (RNot c)      q e = RNot c'
  where
    c' = updateRCond c q e
updateRCond (ROr l r)     q e = ROr l' r'
  where
    l' = updateRCond l q e
    r' = updateRCond r q e
updateRCond (RAnd l r)    q e = RAnd l' r' 
  where
    l' = updateRCond l q e
    r' = updateRCond r q e

-- | updates the qualifier of an attribute atom.
-- TODO: i may need to get the most outermost name instead of lookup
updateAtom :: Atom -> RAlgebra -> RenameEnv -> Atom
updateAtom at@(Att a) _ e 
  | isNothing aq = at 
  | isQualRel (fromJust aq) = Att $
    updateAttrQual 
      a 
      (SubqueryQualifier (fromJust (SM.lookup (relQualifier (fromJust aq)) e)))
  | otherwise    = at
    where
      aq = qualifier a 
updateAtom v       _ _ = v

-- | updates the existing qualifier of attributes in a join condition. 
updateJoinCond :: RCondition 
               -> RAlgebra -> RAlgebra -> RenameEnv
               -> RCondition
updateJoinCond c@(RLit _)      _ _ _ = c 
updateJoinCond (RComp o la ra) l r e = RComp o la' ra'
  where
    la' = updateAtom la l e
    ra' = updateAtom ra r e
updateJoinCond (RNot c)        l r e = RNot c'
  where
    c' = updateJoinCond c l r e
updateJoinCond (ROr lc rc)     l r e = ROr lc' rc' 
  where
    lc' = updateJoinCond lc l r e
    rc' = updateJoinCond rc l r e
updateJoinCond (RAnd lc rc)    l r e = RAnd lc' rc'
  where
    lc' = updateJoinCond lc l r e
    rc' = updateJoinCond rc l r e