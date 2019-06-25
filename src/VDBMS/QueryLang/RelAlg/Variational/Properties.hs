-- | Configuration semantics of vquery. 
module VDBMS.QueryLang.RelAlg.Variational.Properties (

        equivVqs

) where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
import VDBMS.Features.Config
-- import VDBMS.Variational.Opt
-- import VDBMS.Variational.Variational

-- Issues:
-- * equivalency of queries (and confedQs) is wrong!
-- * you should move equivVqs to some test file.


-- | checks whether two configured queries are equivalent or not.
--   need to rewrite this! because == won't cut it!
equivConfedQs :: Algebra -> Algebra -> Bool
equivConfedQs = (==)

-- | checks commuting diagram for a variaitonal query.
equivVqs :: [Config Bool] -> Algebra -> Algebra -> Bool
equivVqs cs q q' = undefined
-- and $ zipWith equivConfedQs confq confq'
 --  where 
 --    confq  = map (configure q) cs
 --    confq' = map (configure q') cs 


