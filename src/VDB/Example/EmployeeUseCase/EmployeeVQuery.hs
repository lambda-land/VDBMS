-- | fold a list of plain query into one v-query 
module VDB.Example.EmployeeUseCase.EmployeeVQuery where

import VDB.Algebra
import qualified VDB.Condition as C
import VDB.Example.EmployeeUseCase.EmployeeQuery
import VDB.Example.EmployeeUseCase.EmployeeSchema
import VDB.Example.EmployeeUseCase.EmployeeVSchema


import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Schema
import VDB.Type
import VDB.Variational
import qualified Data.Map.Strict as M

import Database.HDBC 
import Prelude hiding (EQ, NEQ, LT ,LTE ,GTE,GT)
import Data.Tuple(swap)

--
-- ** Qualify query
--
qualifyQuery :: Schema -> Algebra -> Algebra
qualifyQuery  = undefined 

-- | make a Attribute Relation Map based on gaven schema 
--   ** Noted that can only works good with unique attritbue and relation in schema. 
--      If the shcema contains more than one relation for the same attribute, the last attribtue for the key is retained  
makeAttrRelMap :: Schema -> M.Map Attribute Relation 
makeAttrRelMap (sf, relAttrMap) = let relAttrsList' = (M.toList relAttrMap)
                                      relAttrsList  = map (\(rel, (af, attrTypeMap)) ->(rel, (M.keys attrTypeMap))) relAttrsList'
                                  in  M.fromList $ helper relAttrsList 
                          where helper :: [(Relation, [Attribute])] -> [(Attribute,Relation)]
                                helper []                 = []
                                helper ((rel, attrlist):xs) = (createRelAttrList rel attrlist)  ++ helper xs 
                                createRelAttrList :: Relation -> [Attribute] -> [(Attribute,Relation)]
                                createRelAttrList rel []     = []
                                createRelAttrList rel (x:xs) =  (x, rel) : createRelAttrList rel xs



--
--  ** Variationize Query
-- 

-- | fold a list of plain query into one v-query 
variationizeQuery :: [Algebra] -> Algebra
variationizeQuery qList = pushChoiceDownToSubExpr $ foldQuery qList 1


-- | fold a list of plain query/algebra in to a variational query 
--   with form vn<... v2< q2, v1<q1, Empty>>>
foldQuery :: [Algebra] -> Int -> Algebra
foldQuery []     c = Empty 
foldQuery (x:xs) c = case x of 
                      (SetOp op l r) -> let left = AChc (genFeatureExpr c) l $ foldQuery xs (c+1) 
                                            right = AChc (genFeatureExpr c) r $ foldQuery xs (c+1) 
                                        in (SetOp op left right)
                      _              -> AChc (genFeatureExpr c) x $ foldQuery xs (c+1) 
                      where genFeatureExpr :: Int -> F.FeatureExpr
                            genFeatureExpr i  = let v = "v" ++ show i 
                                                in F.Ref $ Feature v

-- | push the F into l r in term of F<l,r> or F<l,r> 'SetOp' F'<l',r'>
pushChoiceDownToSubExpr :: Algebra -> Algebra
pushChoiceDownToSubExpr Empty           = Empty
pushChoiceDownToSubExpr (SetOp op l r)  = let left = (pushChoiceDownToSubExpr l)
                                              right = (pushChoiceDownToSubExpr r)
                                           in SetOp op left right
pushChoiceDownToSubExpr (AChc  v  l  r) = let x = pushFeatureToAlgebra v l
                                              xs = pushChoiceDownToSubExpr r
                                           in mergeAlgebraFeature x xs 


-- | push down the feature down to smallest parts
pushFeatureToAlgebra :: F.FeatureExpr -> Algebra -> Algebra
pushFeatureToAlgebra f (SetOp op l r)  = SetOp op (pushFeatureToAlgebra f l) (pushFeatureToAlgebra f r)
pushFeatureToAlgebra f (Proj  alist a) = let alist' = map (\(_, attr) -> (f, attr)) alist 
                                         in Proj alist' (pushFeatureToAlgebra f a)
pushFeatureToAlgebra f (Sel   cond  a) = let cond' = C.CChc f cond (C.Lit True)
                                         in Sel cond' (pushFeatureToAlgebra f a)
pushFeatureToAlgebra f (AChc  v  l  r) = let left = pushFeatureToAlgebra v l
                                             right = pushFeatureToAlgebra v r
                                         in (AChc  v  left right)  
pushFeatureToAlgebra f r@(TRef  rel)   = AChc f r (Empty)
pushFeatureToAlgebra _ Empty           = Empty


-- | fold the featureExpr of two v-algebra and get new v-algebra 
mergeAlgebraFeature :: Algebra -> Algebra -> Algebra
mergeAlgebraFeature a                     (SetOp op l r)    = let left = mergeAlgebraFeature a l
                                                                  right = mergeAlgebraFeature a r
                                                              in SetOp op left right 
mergeAlgebraFeature left@(SetOp op l r)         a           = let left = mergeAlgebraFeature l a 
                                                                  right = mergeAlgebraFeature r a 
                                                              in SetOp op left right 
  -- error $ "shouldn't have algebra with SetOp in left alternative of merge procsess" ++"   "++ "left:" ++ show left ++ "a:" ++ show a
mergeAlgebraFeature (Proj  alist1 a1)     (Proj  alist2 a2) = let alist' = mergeAttrList alist1 alist2 
                                                              in  Proj alist' (mergeAlgebraFeature a1 a2)
mergeAlgebraFeature (Sel   cond1  a1)     (Sel   cond2  a2) = let cond' = mergeCond cond1 cond2 
                                                              in  Sel cond' (mergeAlgebraFeature a1 a2)
mergeAlgebraFeature a1@(Sel cond rel)     a2@(AChc v l r)   = Sel cond (mergeAlgebraFeature rel a2) 
mergeAlgebraFeature a1@(AChc f l r)       a2@(Sel cond rel) = Sel cond (mergeAlgebraFeature a1 rel)                                       
mergeAlgebraFeature a1@(AChc f1  l1  r1) a2@(AChc  f2  l2  r2) = if l1 == l2  -- apply choice-join rules
                                                                  then AChc (f1 `F.Or` f2) l1 r1
                                                                  else AChc f2 l2 a1
mergeAlgebraFeature a                 Empty                 = a 
mergeAlgebraFeature Empty                 a                 = a  -- To be verified 

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
mergeCond c1@(C.CChc f1  l1  r1) (C.CChc    f2  l2  _) = if l1 == l2
                                                            then C.CChc (f1 `F.Or` f2) l1 r1
                                                            else C.CChc f2 l2 c1 



--
-- ** small test suite
--

testq1,testq2, testq3, testq4, testq5 :: Algebra

-- SELECT A1 FROM T1
testq1 = Proj [plainAttr "A1" ] $ TRef (Relation "T1")

-- SELECT A2 FROM T2 Where A2 > 5
testq2 =  Proj [plainAttr "A2"] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))

-- SELECT A1, A2 FROM T2 Where A2 > 5
testq2' = Proj [plainAttr "A1",plainAttr "A2" ] $ Sel cond $ TRef (Relation "T2")
         where cond = C.Comp GT (C.Attr (Attribute Nothing "A2")) (C.Val (SqlInt32 5))

-- SELECT A3 FROM T3
testq3 = Proj [plainAttr "A3" ] $ TRef (Relation "T3")

-- (SELECT A1 FROM T2) Union (SELECT A1 FROM T3)
testq4 = SetOp Prod l r 
        where l = Proj [plainAttr "A1" ] $ TRef (Relation "T2")
              r = Proj [plainAttr "A1" ] $ TRef (Relation "T3")

-- SELECT * FROM D,E
testq5 = SetOp Prod (TRef (Relation "D")) (TRef (Relation "E"))

testq6 = SetOp Prod testq2 testq2


-- (SetOp Prod (SetOp Prod 
--               (AChc v1 OR v2 (TRef (Relation {relationName = "empacct"})) Empty) 
--               (AChc v2 (TRef (Relation {relationName = "empacct"})) (AChc v1 (TRef (Relation {relationName = "empbio"})) Empty))) 
--             (SetOp Prod (AChc v2 (TRef (Relation {relationName = "empbio"})) (AChc v1 (TRef (Relation {relationName = "empacct"})) Empty)) 
--                         (AChc v1 OR v2 (TRef (Relation {relationName = "empbio"})) Empty))))

