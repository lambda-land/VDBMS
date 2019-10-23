-- | pushs the vschema onto the query so that
--   configuring a query without passing the schema
--   would result in the correct relational query.
module VDBMS.QueryGen.VRA.PushSchToQ (

       pushSchToQ

)where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.VDB.Name
import VDBMS.VDB.GenName

-- | pushes the schema onto the vq after type checking 
--   the query. in order for the commuting diagram to
--   hold.
pushSchToQ :: Schema -> Algebra -> Algebra
pushSchToQ s (SetOp o l r) = undefined
pushSchToQ s (Proj as rq) = undefined
pushSchToQ s (Sel c rq) 
  = Sel (pushSchToCond s c) (renameMap (pushSchToQ s) rq)
pushSchToQ s (AChc f l r) 
  = AChc f (pushSchToQ s l) (pushSchToQ s r)
pushSchToQ s (Join rl rr c) 
  = Join (renameMap (pushSchToQ s) rl) (renameMap (pushSchToQ s) rr) c
pushSchToQ s (Prod rl rr) 
  = Prod (renameMap (pushSchToQ s) rl) (renameMap (pushSchToQ s) rr)
pushSchToQ s q@(TRef rr) 
  = Proj (relSchToOptAtts (thing rr) s) (renameNothing q)
pushSchToQ s Empty = Empty


-- | takes a relation and schema and generates
--   the list of optattributes of the relationschema
--   in the schema.
relSchToOptAtts :: Relation -> Schema -> OptAttributes
relSchToOptAtts = undefined

-- | pushes schema to vsqlcond.
pushSchToCond :: Schema -> VsqlCond -> VsqlCond
pushSchToCond = undefined

