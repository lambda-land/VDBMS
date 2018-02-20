module PARSER.ParsingSQL where 

--  
-- Concrete syntax for VDB.SQL
-- 

-- | Rname ::= (any relation name)
-- | attrName ::= (any attribute name)
-- | attr ::= attrName
--          | CHOICE (featureExpr,attr,attr)
-- | attrList ::= attr
--              | attr,attrList
-- | vRelation ::= [Rname: attrList]
-- | vRelationList ::= vRelation 
--                   | vRelation,vRelationList
-- | vSchema ::= featureExpr ? {vRelationList}

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

-- | tableName ::= (any table name)
-- | table ::=  tableName 
--           | CHOICE (featureExpr,table ,table)
-- | tableList ::= table 
--               | table CROSSJOIN tableList

-- | query ::= SELECT attrList FROM tableList WHERE condition


-- | feature ::= (any feature name)
-- | featureExpr∷= bool
--               | feature 
--               | !featureExpr
--               | featureExpr ∧featureExpr 
--               | featureExpr ∨featureExpr 

