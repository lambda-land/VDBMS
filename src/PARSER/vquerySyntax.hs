module VquerySyntax where

-- | AST for V-schema
-- |
-- | Rname∶≔(any relation name)
-- | attr∶≔(any attribute name)
-- | attrSet∶≔ε | attr,attrSet 
-- | vSet∶≔{attrSet}
-- |      | vSet ∪vSet  
-- |      | f<vSet,vSet> 
-- | vRelation∶≔[Rname∶vSet]
-- | vRelationList∶≔ ε | vRelation,vRelationList
-- | vSchema∶≔f<{vRelationList},∅>

type Rname = String
type Attr = String
type Aset = [String]
data Vset = AttrSet Aset
          | VsetUnion Vset Vset
          | VsetF FeatureDim Vset Vset
data Vrelation = RVset Rname Vset
type Vrelations = [Vrelation]
data VSchema = Vsch FeatureDim Vrelations 

-- | Concrete syntax for V-Query
-- |
-- | const∶≔(any constant value)
-- | vtable∶≔(any vtable name)
-- | vtables∶≔ε | vtable,vtables 
-- | opt∶≔ <|<=|=|>|>=|  !=   
-- | vCondition∷= tag
-- |            | attr opt const 
-- |            | attr opt attr
-- |            | !vCondition
-- |            | vCondition OR vCondition
-- |            | vCondition AND vCondition
-- |            | f<vCondition ,vCondition>	
-- | query∶≔SELECT vSet FROM vtables WHERE vCondition
-- | vQuery∶≔query
-- |        | f<query,query> 

data Const = I Int 
           | S String
type Vtable = String
type Vtables = [Vtable]
data Opt = Less | LessEqul | Equal | Greater | GreaterEqul | NotEqual
data Vcond = T Tag 
           | AttrOptC Attr Opt Const
           | AttrOptA Attr Opt Attr
           | NotCond Vcond
           | OrCond Vcond Vcond 
           | AndCond Vcond Vcond 
           | VcondF FeatureDim Vcond Vcond 
data Query = SelectFromWhere Vset Vtables Vcond 
data VQuery = Single Query
            | VQueryF FeatureDim Query Query 

-- | Concrete syntax for feature formula

-- | feature∶≔(any feature name) 
-- | tag∶≔True | False 
-- | conjFeature∷=feature
-- |             | conjFeature ∧ conjFeature
-- | disjFeature∶≔ conjFeature ∨ feature 
-- |             |conjFeature ∨conjFeature
-- |            
-- | f∷= conjFeature | disjFeature 

type Feature = String
type Tag = Bool
data ConjFeature = F Feature 
                 | Conj ConjFeature ConjFeature
data DisjFeature = DisjCF ConjFeature Feature
                 | DisjCC ConjFeature ConjFeature
data FeatureDim = Fconj ConjFeature
                 | Fdisj DisjFeature             

