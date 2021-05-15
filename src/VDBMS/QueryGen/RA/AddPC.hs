-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.RA.AddPC (

         -- addPC

) where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra (RAlgebra(..))
import VDBMS.VDB.Name (PCatt)
import VDBMS.QueryLang.RelAlg.Variational.SmartConstructor (att2attr)

addPC :: PCatt -> RAlgebra -> RAlgebra
addPC p (RSetOp o l r)   = RSetOp o (addPC p l) (addPC p r)
addPC p (RProj as q)     = RProj (as ++ pure (att2attr p)) (addPC p q)
addPC p (RSel c q)       = RSel c (addPC p q)
addPC p (RJoin l r c)    = RJoin (addPC p l) (addPC p r) c
addPC p (RProd l r)      = RProd (addPC p l) (addPC p r)
addPC p (RTRef r)        = RTRef r
addPC p (RRenameAlg n q) = RRenameAlg n (addPC p q)
addPC _ REmpty           = REmpty
