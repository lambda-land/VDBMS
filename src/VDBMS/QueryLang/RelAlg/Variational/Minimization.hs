-- | Variation minimization of variational relational queries.
module VDBMS.QueryLang.RelAlg.Variational.Minimization where 

import VDBMS.QueryLang.RelAlg.Variational.Algebra
-- import VDBMS.Features.Config
-- import VDBMS.QueryLang.ConfigQuery
-- import VDBMS.Variational.Opt
-- import VDBMS.Variational.Variational

-- | Applies the minimization rules until the query doesn't change.
appMin :: Algebra -> Algebra
appMin = undefined 

-- | Variation minimization rules.
-- Note: not sure which side is more optimized. We can determine that by
--       running some experiments. It also probably depends on the 
--       approach we take.
minVar :: Algebra -> Algebra 
minVar = undefined