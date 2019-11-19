-- | Tests to check validity of a vschema. 
module VDBMS.VDB.Schema.Variational.Tests (

        isVschValid

) where

import VDBMS.Features.SAT
import VDBMS.VDB.Schema.Variational.Schema

-- | checks 1) if fm is sat, 2) if all relations
--   pc are sat, and 3) if all atts pc are sat.
isVschValid :: Schema -> Bool 
isVschValid = undefined

-- | checks if the feature model is satisfiable. 
satFM :: Schema -> Bool
satFM = satisfiable . featureModel

-- | checks if a relation pc is satisfiable. 
-- satRPC :: Schema -> Bool 

-- | checks all relations in a schema to see if
--   their pc is satisfiable.


-- | checks if an attribute pc is satisfiable.


-- | checks if all attributes of a relation have 
--   satisfiable pc.

-- | check if all attributes of all relations of 
--   the schema have satisfiable pc.
