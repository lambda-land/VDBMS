-- | Typed symbol domains.
module VDBMS.VDB.GenName (

       rename 
       , rerename
       , renameNothing
       , relQual
       , subqQual

) where

import VDBMS.VDB.Name

-- import Data.Data (Data,Typeable)
-- import Data.String (IsString)

-- import Data.Set (Set)
-- import qualified Data.Set as Set (fromList)

-- | creates a rename for a given thing.
rename :: Name -> a -> Rename a 
rename n a = Rename (Just n) a

-- | re-renames a given rename thing.
rerename :: Name -> Rename a -> Rename a
rerename n (Rename (Just a) t) = Rename (Just n) t
rerename n (Rename Nothing t)  = Rename (Just n) t

-- | creates a rename with no name for a thing.
renameNothing :: a -> Rename a 
renameNothing a = Rename Nothing a

-- | generates a relation qualifier for a given name.
relQual :: Name -> Qualifier
relQual n = RelQualifier $ Relation n

-- | generates a subquery qualifier for a given name.
subqQual :: Name -> Qualifier
subqQual n = SubqueryQualifier n

