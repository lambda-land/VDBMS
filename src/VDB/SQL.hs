module VDB.SQL where

import VDB.FeatureExpr
import VDB.Name
import VDB.Condition


--
-- * Syntax for SQL
--


-- | An attrList is a list of Attribute. Empty list is not allowed.
data AttrList 
   = A Attribute  
   | AttrChc FeatureExpr AttrList AttrList
   | AConcat AttrList AttrList
  deriving (Eq,Show)


-- | A Table is a list of table. Empty list is not allowed. 
data RelationList 
   = R Relation
   | RelChc FeatureExpr RelationList RelationList 
   | CROSSJOIN RelationList RelationList
  deriving (Eq,Show)

-- | Query expression. SELECT ... FROM ... WHERE ...
data Query = SELECT AttrList FromExpr WhereExpr
           | QChc FeatureExpr Query Query
  deriving (Eq,Show)


-- | FROM ... 
data FromExpr  = FROM RelationList
  deriving (Eq,Show)

-- | Where ...
data WhereExpr = WHERE Condition 



-- | A Vrelation is the name of variational relation and its corresponding attribute list.
data Vrelation = VR Relation AttrList
   deriving (Eq,Show)

-- 
-- * Traditional schema in SQL
--   (Define a schema in traditional SQL by create one table per time)
-- 


-- | Type expression for data
data DataType = I | B | S | NULL

-- | Associate attribute with datatype
data AttrAndType = AT Attibute DataType

-- | List of combined Attribute and dataType
data AttrAndTypeList 
   = SingleAT AttrAndType
   | ATList   AttrAndType AttrAndTypeList

-- | CREATE TABLE expression
data CreateRelation = CreateTable Relation AttrAndTypeList


--
-- * Variational schema
--  (Relation associated with varialtional relation) 
-- 

-- | VRelation is a relation associated with attrList
data VRelation = VR Relation AttrList

-- | A VrelationList is a list of Vrelaiton which will contribute to a v-schema.
--   Empty list is not allowed. 
data VRelationList 
   = VRelation 
   | VRConcat VRelation VRelationList
  deriving (Eq,Show)

-- | A v-schema involved with featureExpr. 
data VSchema = ScheCHOICE FeatureExpr VRelationList
  deriving (Eq,Show)
