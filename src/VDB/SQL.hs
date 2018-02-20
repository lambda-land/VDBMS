module VDB.SQL where

import VDB.FeatureExpr
import VDB.Name
import VDB.Condition


--
-- * Syntax for SQL
--

-- | An Attr is an Attribute together with its feature choices.
data Attr = Attribute  
          | AttrCHOICE FeatureExpr Attribute Attribute
  deriving (Eq,Show)

-- | An attrList is a list of Attr. Empty list is not allowed.
data AttrList 
   = Attr 
   | AttrConcat Attr AttrList
  deriving (Eq,Show)

-- | A Rname is the name of relation.
type Rname = String

-- | A Vrelation is the name of variational relation and its corresponding attribute list.
data Vrelation = VR Rname AttrList
   deriving (Eq,Show)

-- | A VrelationList is a list of Vrelaiton which will contribute to a v-schema.
--   Empty list is not allowed. 
data VRelationList 
   = Vrelation 
   | RConcat Vrelation VRelationList
  deriving (Eq,Show)

-- | A v-schema involved with featureExpr. 
data VSchema = ScheCHOICE FeatureExpr VRelationList
  deriving (Eq,Show)

-- | A TableName is the name of a table. 
--   Table is different with the relation. 
type TableName = String

-- | A Table associated with featureExpr. 
data Table
   = TableName 
   | TableCHOICE FeatureExpr Table Table 
  deriving (Eq,Show)

-- | A Table is a list of table. Empty list is not allowed. 
data TableList 
   = Table 
   | CROSSJOIN Table TableList
  deriving (Eq,Show)

-- | Query expression.
data Query = SFW AttrList TableList Condition  
  deriving (Eq,Show)


