module VDB.SQL where

import VDB.FeatureExpr
import VDB.Name
import VDB.Condition



import VDB.Variational 

--
-- * Abstract Syntax for SQL
--

-- | An attrList is a list of Attribute. Empty list is not allowed.
type AttrList = [Opt Attribute]

-- | A RelationList is a list of relation / Choice of relation. Empty list is not allowed. 
type RelationList = [Opt Relation]

-- | Query expression. SELECT ... FROM ... WHERE ...
data VQuery = VSelect AttrList RelationList (Maybe Condition)
            | QChc FeatureExpr VQuery VQuery
  deriving (Eq,Show)



--  
-- Concrete syntax for VDB.SQL
-- 


-- | attribute ::= (any attribute name)

-- | attrList ::= attribute 
--              | CHOICE (featureExpr,attrList,attrList)
--              | CHOICE (featureExpr,attrList)
--              | attrList, attrList


-- | relaiton ::= (any relation name)

-- | relationList ::= relation 
--                  | CHOICE (featureExpr,relationList ,relationList)
--                  | CHOICE (featureExpr,realtionList)
--                  | relationList, relationList


-- | int ::= (Any integer)
-- | bool ::= (Any Boolean value)
-- | string ::= (any string value)

-- | atom ::= int | bool | string | attr  
-- | opt ::= <| <= | = | > | >= | !=   
-- | condition ∷= atom opt atom 
--              | NOT condition
--              | condition OR condition
--              | condition AND condition
--              | CHOICE (featureExpr,conditon ,condition)  

-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | NOT featureExpr
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

