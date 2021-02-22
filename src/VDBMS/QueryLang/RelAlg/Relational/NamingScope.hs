-- | it names every subquery if it's not renamed already
--   and adjusts the qualifier of attirubtes both in 
--   projection and conditions. note that if conditions
--   don't have qualifiers it won't add them because
--   they won't matter since the input query is type-correct.
module VDBMS.QueryLang.RelAlg.Relational.NamingScope where


import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name

import Control.Monad.State

import qualified Data.Map as M 
import qualified Data.Map.Strict as SM

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
-- nameSubqRA = undefined
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
updateAttsQual as q e = undefined
  -- map (flip (flip updateAttQual q) q') as

-- | updates the attribute qualifier if it has one. from the 
--   old query q to the new query q'. 
-- updateAttQual :: Attr -> RAlgebra -> RAlgebra -> Attr
-- updateAttQual a q q' = undefined


-- -- | updates the existing qualifier of attributes in a condition. 
updateCond :: SqlCond RAlgebra -> RAlgebra -> RenameEnv -> SqlCond RAlgebra
updateCond = undefined
-- updateCond (SqlCond c)  q q' = SqlCond $ updateRCond c q q'
-- updateCond c@(SqlIn _ _) _ _ = c
-- updateCond (SqlNot c)   q q' = SqlNot c'
--   where
--     c' = updateCond c q q' 
-- updateCond (SqlOr l r)  q q' = SqlOr l' r'
--   where
--     l' = updateCond l q q' 
--     r' = updateCond r q q'
-- updateCond (SqlAnd l r) q q' = SqlAnd l' r' 
--   where
--     l' = updateCond l q q' 
--     r' = updateCond r q q'

-- -- |
-- updateRCond :: RCondition -> RAlgebra -> RAlgebra -> RCondition
-- updateRCond c@(RLit _)    _ _  = c
-- updateRCond (RComp o l r) q q' = RComp o l' r' 
--   where 
--     l' = updateAtom l q q'
--     r' = updateAtom r q q'
-- updateRCond (RNot c)      q q' = RNot c'
--   where
--     c' = updateRCond c q q'
-- updateRCond (ROr l r)     q q' = ROr l' r'
--   where
--     l' = updateRCond l q q'
--     r' = updateRCond r q q' 
-- updateRCond (RAnd l r)    q q' = RAnd l' r' 
--   where
--     l' = updateRCond l q q'
--     r' = updateRCond r q q' 

-- -- | 
-- updateAtom :: Atom -> RAlgebra -> RAlgebra -> Atom
-- updateAtom a q q' = undefined

-- -- | updates the existing qualifier of attributes in a join condition. 
updateJoinCond :: RCondition 
               -> RAlgebra -> RAlgebra -> RenameEnv
               -> RCondition
updateJoinCond = undefined
-- updateJoinCond c@(RLit _)      _ _ _  _  = c 
-- updateJoinCond (RComp o la ra) l r l' r' = RComp o la' ra'
--   where
--     la' = updateAtom la l l'
--     ra' = updateAtom ra r r'
-- updateJoinCond (RNot c)        l r l' r' = RNot c'
--   where
--     c' = updateJoinCond c l r l' r'
-- updateJoinCond (ROr lc rc)     l r l' r' = ROr lc' rc' 
--   where
--     lc' = updateJoinCond lc l r l' r'
--     rc' = updateJoinCond rc l r l' r'
-- updateJoinCond (RAnd lc rc)    l r l' r' = RAnd lc' rc'
--   where
--     lc' = updateJoinCond lc l r l' r'
--     rc' = updateJoinCond rc l r l' r'