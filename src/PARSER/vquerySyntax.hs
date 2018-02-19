module VquerySyntax where


import VDB.Condition.hs
import VDB.FeatureExpr.hs
--| Concrete Syntax and AST for V-schema
--|
--| Rname ∶:= (any relation name)
--| attrName ∶:= (any attribute name)
--| attr ::= attrName | CHOICE (featureExpr,attr,attr)
--| attrList ::= attr | attr,attrList
--| vRelation ::= [Rname: attrList]
--| vRelationList ::= vRelation | vRelation,vRelationList
--| vSchema ::= featureExpr ? {vRelationList}


type Rname = String
type AttrName = String
type Attr = AttrName | AttrCHOICE FeatureExpr Attr Attr
data AttrList = Attr | AttrConcat Attr AttrList
data Vrelation = VR Rname AttrList
type VRelationList = Vrelation | RConcat Vrelation VRelationList
data VSchema = ScheCHOICE FeatureExpr VRelationList

--| Concrete Syntax and AST for Query 
--|
--| const::=(any constant value)
--| tableName ::= (any table name)
--| table ::=  tableName | CHOICE (featureExpr,table ,table)
--| tableList ::=   table | table CROSSJOIN tableList
--| opt ::=  <|<=|=|>|>=|  !=   
--| condition ∷= tag
--|            | attr opt const 
--|            | attr opt attr
--|            | !condition
--|            | condition OR condition
--|            | condition AND condition
--|            | CHOICE (featureExpr,conditon ,condition)		
--|query ::= SELECT attrList FROM tableList WHERE condition


-- | Comparison operators from VDB/Condition.hs
-- data Op = LT | LTE | GTE | GT | EQ | NEQ
--   deriving (Data,Eq,Show,Typeable)

-- | Conditions from VDB/Condition.hs.
-- data Condition
--    = Comp Op Atom Atom
--    | Not  Condition
--    | Or   Condition Condition
--    | And  Condition Condition
--    | CChc FeatureExpr Condition Condition
--   deriving (Data,Eq,Show,Typeable)

type TableName = String
type Table = TableName | TableCHOICE FeatureExpr Table Table 
type TableList = Table | CROSSJOIN Table TableList

data Query = SFW AttrList TableList Condition  


--| feature ::= (any feature name) 
--| tag ::= True | False 
--| conjFeature ∷= feature
--|              | conjFeature∧ conjFeature
--| disjFeature ::= conjFeature ∨conjFeature
--|               | conjFeature ∨feature 
--| featureExpr∷= conjFeature | disjFeature 

-- ****???? TO DO
-- type Feature = String
-- type Tag = Bool
-- data ConjFeature = F Feature 
--                  | Conj ConjFeature ConjFeature
-- data DisjFeature = DisjCF ConjFeature Feature
--                  | DisjCC ConjFeature ConjFeature
-- data FeatureExpr = Fconj ConjFeature
--                  | Fdisj DisjFeature             

