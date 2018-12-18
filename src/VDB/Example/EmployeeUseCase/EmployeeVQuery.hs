module VDB.Example.EmployeeUseCase.EmployeeVQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import VDB.Example.EmployeeUseCase.EmployeeQuery
import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.EmployeeVSchema


import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Type
import VDB.Variational
import qualified Data.Map.Strict as M

import Database.HDBC 
import Prelude hiding (EQ, NEQ, LT ,LTE ,GTE,GT)
import Data.Tuple(swap)



variationizeQuery :: [Algebra] -> Algebra
variationizeQuery = foldl mergeAlgebraFeature Empty

-- | push the gaven featureExpr to plain algebra(query) and get a v-algebra(V-query)
pushFeatureToAlgebra :: F.FeatureExpr -> Algebra -> Algebra
pushFeatureToAlgebra f (SetOp op l r)  = SetOp op (pushFeatureToAlgebra f l) (pushFeatureToAlgebra f r)
pushFeatureToAlgebra f (Proj  alist a) = let alist' = map (\(_, attr) -> (f, attr)) alist 
                                         in Proj alist' (pushFeatureToAlgebra f a)
pushFeatureToAlgebra f (Sel   cond  a) = let cond' = C.CChc f cond (C.Lit True)
                                         in Sel cond' (pushFeatureToAlgebra f a)
pushFeatureToAlgebra f (AChc  v  l  r) = error "Shouldn't have AChc in palin query/Algebra"  
pushFeatureToAlgebra f r@(TRef  rel)   = AChc f r (Empty)
pushFeatureToAlgebra _ Empty          = Empty

-- | fold the featureExpr of two v-algebra and get new v-algebra 
mergeAlgebraFeature :: Algebra -> Algebra -> Algebra
mergeAlgebraFeature f                     (SetOp op l r)    = undefined -- ?  
mergeAlgebraFeature (Proj  alist1 a1)     (Proj  alist2 a2) = let alist' = mergeAttrList alist1 alist2 
                                                              in  Proj alist' (mergeAlgebraFeature a1 a2)
mergeAlgebraFeature (Sel   cond1  a1)     (Sel   cond2  a2) = let cond' = mergeCond cond1 cond2 
                                                              in  Sel cond' (mergeAlgebraFeature a1 a2)
mergeAlgebraFeature a1@(Sel cond rel)     a2@(AChc v l r)   = Sel cond (mergeAlgebraFeature rel a2) 
mergeAlgebraFeature a1@(AChc f l r)       a2@(Sel cond rel) = Sel cond (mergeAlgebraFeature a1 rel)                                       
mergeAlgebraFeature a1@(AChc f1  l1  r1) a2@(AChc  f2  l2  r2) = if l1 == l2  -- apply choice-join rules
                                                                  then AChc (f1 `F.Or` f2) l1 r1
                                                                  else AChc f2 l2 a1
mergeAlgebraFeature _                     Empty             = Empty
mergeAlgebraFeature Empty                 a                 = a 

-- | merge two opt attribute list into one 
mergeAttrList :: [Opt Attribute] -> [Opt Attribute] -> [Opt Attribute]
mergeAttrList l r = let l' = swapAndMakeMap l
                        r' = swapAndMakeMap r
                    in  map swap $ M.toList  $ M.unionWith unionAttrListHelper l' r'
    where unionAttrListHelper  f1    f2 =  F.shrinkFeatureExpr (f1 `F.Or` f2)
          swapAndMakeMap = M.fromList . (map swap) 

-- | merge two v-cond into one
--   snd condition (c2) will always have pattern: v2 <l2, Lit True>
mergeCond :: C.Condition -> C.Condition -> C.Condition
mergeCond c1@(C.CChc f1  l1  r1) c2@(C.CChc    f2  l2  r2) = if l1 == l2
                                                            then C.CChc (f1 `F.Or` f2) l1 r1
                                                            else C.CChc f2 l2 c1 


--
-- ** small test suite
--

testq1,testq2 :: Algebra
-- SELECT A1 FROM T1
testq1 = pushFeatureToAlgebra v1 $ Proj [plainAttr "A1" ] $ TRef (Relation "T1")
-- SELECT A2 FROM T1 Where A2 > 5
testq2 = pushFeatureToAlgebra v2 $ Proj [plainAttr "A2"] $ Sel cond $ TRef (Relation "T1")
         where cond = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))
-- SELECT 
testq3 = pushFeatureToAlgebra v3 $ Proj [plainAttr "A3" ] $ TRef (Relation "T3")

-- cond1 = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))
-- cond2 = C.Comp GT (C.Attr (Attribute "A2")) (C.Val (SqlInt32 5))
