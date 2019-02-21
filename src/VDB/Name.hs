-- | Typed symbol domains.
module VDB.Name where

import Data.Data (Data,Typeable)
import Data.String (IsString)


-- | A feature is a named, boolean configuration option.
newtype Feature = Feature { featureName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)

-- | An attribute (i.e. column) name.
-- newtype Attribute = Attribute { attributeName :: String }
  -- deriving (Data,Eq,IsString,Ord,Show,Typeable)

data Attribute = Attribute { attributeQualifier :: Maybe Relation, attributeName :: String} 
  deriving (Data,Eq,Ord,Show,Typeable)

-- Attribute n  = Attribute Nothing n 

-- | generates an attribute with a Nothing relation.
genAtt :: String -> Attribute
genAtt a = Attribute Nothing a

-- | adds a relation to an attribute doesn't have a relation yet
--   or update the relation of an attribute.
addRelToAtt :: Attribute -> Relation -> Attribute
addRelToAtt (Attribute Nothing a) r = Attribute (Just r) a
addRelToAtt (Attribute _ a) r       = Attribute (Just r) a

-- | A relation (i.e. table) name.
newtype Relation = Relation { relationName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)

-- | Name of presence condition attribute in db.
newtype PresCondAtt = PresCondAtt { presCondAttName :: String }
  deriving (Data,Eq,IsString,Ord,Show,Typeable)  

-- | A feasible type to use while creating sql tables.
-- newtype CreateSqlTableType = CreateSqlTableType { typeName :: String}
--   deriving (Data,Eq,IsString,Ord,Show,Typeable)  
  
-- test
-- testf:: Feature
-- testf = "A"