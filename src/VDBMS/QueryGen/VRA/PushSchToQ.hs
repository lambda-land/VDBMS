-- | pushs the vschema onto the query so that
--   configuring a query without passing the schema
--   would result in the correct relational query.
module VDBMS.QueryGen.VRA.PushSchToQ where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.VDB.Schema.Variational.Schema

-- | pushes the schema onto the vq after type checking 
--   the query. in order for the commuting diagram to
--   hold.
pushSchToQ :: Schema -> Algebra -> Algebra
pushSchToQ s (SetOp o l r) = undefined
pushSchToQ s (Proj as rq) = undefined
pushSchToQ s (Sel c rq) = undefined
pushSchToQ s (AChc f l r) = undefined
pushSchToQ s (Join rl rr c) = undefined
pushSchToQ s (Prod rl rr) = undefined
pushSchToQ s (TRef rr) = undefined
pushSchToQ s Empty = Empty