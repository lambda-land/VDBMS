-- | it names every subquery if it's not renamed already
--   and adjusts the qualifier of attirubtes both in 
--   projection and conditions. note that if conditions
--   don't have qualifiers it won't add them because
--   they won't matter since the input query is type-correct.
module VDBMS.QueryLang.RelAlg.Relational.NamingScope where


import VDBMS.QueryLang.RelAlg.Relational.Algebra
import VDBMS.VDB.Name

import Control.Monad.State

type AliasNum = Int 

type QState = State AliasNum

-- | evaluate the qstate with zero.
evalQState :: QState a -> a 
evalQState = flip evalState initState
  where initState = 0

-- | gives name to subqueries in a relational algebra query.
nameSubqRAlgebra :: RAlgebra -> RAlgebra
nameSubqRAlgebra = evalQState . nameSubqRA 

-- |
nameSubqRA :: RAlgebra -> QState RAlgebra
nameSubqRA (RSetOp o l r)   = 
  do l' <- nameSubqRA l 
     r' <- nameSubqRA r 
     return $ RSetOp o l' r'
nameSubqRA (RProj as q)     = 
  do q' <- nameSubqRA q 
     s <- get
     let as' = updateAttQual as q q'
         q'' = RProj as' (RRenameAlg ("t" ++ show s) q')
     modify succ
     return q''
nameSubqRA (RSel c q)       = 
  do q' <- nameSubqRA q 
     -- s <- get
     let c'  = updateCond c q q'
         q'' = RSel c' q'
     return q''
nameSubqRA (RJoin l r c)    = 
  do l' <- nameSubqRA l
     r' <- nameSubqRA r 
     let c'  = updateJoinCond c l r l' r' 
         q'' = RJoin l' r' c' 
     return q''
nameSubqRA (RProd l r)      = 
  do l' <- nameSubqRA l
     r' <- nameSubqRA r
     return $ RProd l' r'
nameSubqRA q@(RTRef _)      = 
  return q
nameSubqRA (RRenameAlg n q) = 
  do q' <- nameSubqRA q
     return $ RRenameAlg n q'
nameSubqRA REmpty           = 
  return REmpty

-- |
updateAttQual :: Attributes -> RAlgebra -> RAlgebra -> Attributes
updateAttQual = undefined

-- | 
updateCond :: SqlCond RAlgebra -> RAlgebra -> RAlgebra -> SqlCond RAlgebra
updateCond = undefined

-- |
updateJoinCond :: RCondition 
               -> RAlgebra -> RAlgebra -> RAlgebra -> RAlgebra 
               -> RCondition
updateJoinCond = undefined
