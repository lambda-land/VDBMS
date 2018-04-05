module VDB.SQL where

import VDB.FeatureExpr
import VDB.Name
import VDB.Condition


--  
-- Concrete syntax for VDB.SQL
-- 


-- | attribute ::= (any attribute name)

-- | attrList ::= attribute 
--              | CHOICE (featureExpr,attrList,attrList)
--              | attrList, attrList


-- | relaiton ::= (any relation name)

-- | relationList ::= relation 
--                  | CHOICE (featureExpr,relationList ,relationList)
--                  | relationList, relationList


-- | int ::= (Any integer)
-- | bool ::= (Any Boolean value)
-- | string ::= (any string value)

-- | atom ::= int | bool | string | attr  
-- | opt ::= <| <= | = | > | >= | !=   
-- | condition ∷= atom opt atom 
--              | !condition
--              | condition OR condition
--              | condition AND condition
--              | CHOICE (featureExpr,conditon ,condition)  

-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | !featureExpr
--               | featureExpr  AND featureExpr 
--               | featureExpr OR featureExpr 


-- | query :: = SELECT attrlist fromExpr whereExpr
--            | CHOICE(featureExor, query, query )

-- | fromExpr :: = FROM relationlist 
-- | whereExpr :: = WHERE condition

-- 
-- * Traditional schema in SQL
-- * (Define a schema in traditional SQL by create one table per time)
-- 

-- | dataType ::= (any table type)

-- | attrAndType ::= attribute datatype  

-- | attrAndTypeList ::= attrAndType
--                     | attrAndType, attrAndTypeList

-- | createRelation ::= CREATE TABLE relation (attrAndTypeList);

--
-- * Variational schema
-- * (Relation associated with varialtional relation) 
-- 


-- | vRelation ::= [relation: attrList]
-- | vRelationList ::= vRelation
--                   | vRelaiton, vRelaitonList
-- | vSchema ::= featureExpr ? {vRelationList}


--
-- * Abstract Syntax for SQL Query
--

-- | An attrList is a list of Attribute. Empty list is not allowed.
data AttrList 
   = A Attribute  
   | AttrChc FeatureExpr AttrList AttrList
   | AConcat AttrList AttrList
  deriving (Eq,Show)

-- | A RelationList is a list of relation / Choice of relation. Empty list is not allowed. 
data RelationList 
   = R Relation
   | RelChc FeatureExpr RelationList RelationList 
   | CROSSJOIN RelationList RelationList
  deriving (Eq,Show)

-- | Query expression. SELECT ... FROM ... WHERE ...
data Query = Select AttrList FromExpr WhereExpr
           | QChc FeatureExpr Query Query
  deriving (Eq,Show)

-- | FROM ... 
data FromExpr  = From RelationList
  deriving (Eq,Show)

-- | Where ...
data WhereExpr = Where Condition
  deriving (Eq,Show)

-- | Boolean expressions over features.
data FeatureExpr
   = FLit Bool
   | FRef Feature
   | FNot FeatureExpr
   | FAnd FeatureExpr FeatureExpr
   | FOr  FeatureExpr FeatureExpr
  deriving (Eq,Show)

-- | Atoms are the leaves of a condition.
data Atom
   = Val  Value
   | Attr Attribute
  deriving (Eq,Show)

-- | Variational conditions.
data Condition
   = CLit  Bool
   | CComp CompOp Atom Atom
   | CNot  Condition
   | COr   Condition Condition
   | CAnd  Condition Condition
   | CChc FeatureExpr Condition Condition
  deriving (Eq,Show)

--
-- Abstract syntax for SQL Schema
--

-- | Type expression for data
data DataType = INTEGER | BOOLEAN | VARCHAR | NULL
  deriving (Eq,Show)
-- | Associate attribute with datatype
data AttrAndTypes 
  = AT Attribute DataType
  | ATConcat AttrAndTypes AttrAndTypes
  deriving (Eq,Show)
-- | CREATE TABLE expression
data CreateRelation = CreateTable Relation AttrAndTypes
  deriving (Eq,Show)
type Parser = Parsec Void String

--
-- * Abstract Syntax for Variational schema
--  (Relation associated with varialtional relation) 
-- 

-- | A VrelationList is a list of Vrelaiton which will contribute to a v-schema.
--   Empty list is not allowed. 
data VRelationList 
   = VR Relation AttrList
   | VRConcat VRelationList  VRelationList 
  deriving (Eq,Show)

-- | A v-schema involved with featureExpr. 
data VSchema = ScheCHOICE FeatureExpr VRelationList 
  deriving (Eq,Show)
