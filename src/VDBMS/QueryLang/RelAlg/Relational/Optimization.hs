-- | relational alg optimization rules.
module VDBMS.QueryLang.RelAlg.Relational.Optimization (

       opts
       , opts_
       -- appOpt
       -- , appOpt_

)where 

import VDBMS.QueryLang.RelAlg.Relational.Algebra 
-- import qualified VDBMS.Features.FeatureExpr.FeatureExpr as F
import VDBMS.VDB.Name
import VDBMS.TypeSystem.Relational.TypeSystem
import VDBMS.VDB.Schema.Relational.Types
-- -- import VDBMS.Features.Config
-- -- import VDBMS.QueryLang.ConfigQuery
-- import VDBMS.Variational.Opt (mapFst, getObj, getFexp, applyFuncFexp, mkOpt)
-- -- import VDBMS.Variational.Variational

-- import qualified Data.Map as M 
import qualified Data.Map.Strict as SM (lookup)
import Data.Maybe (catMaybes, fromJust)
import Data.List (partition)

import Data.Generics.Uniplate.Operations (transform)

-- | Applies the minimization rules until the query doesn't change.
-- only the ones that don't ask for schema.
appOpt_ :: RAlgebra -> RAlgebra
appOpt_ q
  | opts_ q == q  = q 
  | otherwise     = appOpt_ (opts_ q)

-- | Relational optimization rules. only the ones that don't ask for schema.
opts_ :: RAlgebra -> RAlgebra 
opts_ = optRSelRec . pushOutRProjRec


-- | Applies the minimization rules until the query doesn't change.
-- appOpt :: RAlgebra -> RSchema -> RAlgebra
-- appOpt q s
--   | opts q s == q = q 
--   | otherwise     = appOpt (opts s q) s

-- | Relational optimization rules.
opts :: RSchema -> RAlgebra -> RAlgebra 
opts s q = 
  selRDistrRec s ((optRSelRec . pushOutRProjRec) q)

-- | recursive application of push out prj.
pushOutRProjRec :: RAlgebra -> RAlgebra
pushOutRProjRec = transform pushOutRProj

-- | Pushes out projection as far as possible.
-- Note that you don't necessarily want to push out all projs.
-- Eg: proj l1 R * proj l2 S = proj (l1 + l2) (R * S)
--     but the rhs isn't more efficient than the lhs! keep in 
--     min that the same goes for joins.
-- There are also cases that you CANNOT push out projs:
-- Eg: proj l1 q1 `union` proj l1 q2 <> proj l1 (q1 `union` q2)
pushOutRProj :: RAlgebra -> RAlgebra
-- σ c (π l q) ≡ π l (σ c q)
pushOutRProj (RSel c (RProj as q))
  = RProj as (RSel c (pushOutRProj q))
-- π l₁ (π l₂ q) ≡ π l₁ q
-- checks if renaming happened in l₂ and update 
-- l₁ appropriately! 
pushOutRProj (RProj as1 (RProj as2 q))
  = RProj as1 q
  -- = RProj (updateAtts as1 as2) (renameMap pushOutRProj rq)
  --   where
  --     updateAtts :: Attributes -> Attributes -> Attributes
  --     updateAtts orgs subs = [ compAtts a subs | a <- orgs]
  --     compAtts :: Rename Attr -> Attributes -> Rename Attr
  --     compAtts a as 
  --       | null attList = a 
  --       | otherwise = head attList 
  --         where attList = catMaybes [ compAtt a att | att <- as]
  --     compAtt :: Rename Attr -> Rename Attr -> Maybe (Rename Attr)
  --     compAtt a1 a2 
  --       | name a2 == Nothing 
  --           = Just (Rename (name a1) (thing a2))
  --       | name a2 /= Nothing 
  --         && (attributeName . attribute . thing) a1 == (fromJust (name a2))
  --           = Just a2
  --       | otherwise = Nothing
-- pushOutRProj (RSetOp o q1 q2)
--   = RSetOp o (pushOutRProj q1) (pushOutRProj q2)
-- pushOutRProj (RJoin q1 q2 c)
--   = RJoin (pushOutRProj q1) (pushOutRProj q2) c
-- pushOutRProj (RProd q1 q2) 
--   = RProd (pushOutRProj q1) (pushOutRProj q2)
-- pushOutRProj (RRenameAlg n q) = RRenameAlg n (pushOutRProj q)
pushOutRProj q = q 

-- | checks if a sql condition is of the form "attr in query" condition.
notInCond :: SqlCond RAlgebra -> Bool 
notInCond (SqlIn _ _)     = True
notInCond (SqlCond _)     = False
notInCond (SqlNot c)      = notInCond c
notInCond (SqlOr l r)     = notInCond l && notInCond r
notInCond (SqlAnd l r)    = notInCond l && notInCond r 

-- | knowing that the sql condition is not of the form "attr in query"
--   converts the sql condition to a relational condition.
relCond :: SqlCond RAlgebra -> RCondition
relCond (SqlCond c)     = c 
relCond (SqlIn _ _)     = error $ "didn't expect to get a condition of the form attr in query!! QUERY VAR MIN!!"
relCond (SqlNot c)      = RNot (relCond c)
relCond (SqlOr l r)     = ROr (relCond l) (relCond r)
relCond (SqlAnd l r)    = RAnd (relCond l) (relCond r)

-- | recurssive application of optrsel.
optRSelRec :: RAlgebra -> RAlgebra
optRSelRec = transform optRSel

-- | optimizes the selection queries.
optRSel :: RAlgebra -> RAlgebra
-- σ c₁ (σ c₂ q) ≡ σ (c₁ ∧ c₂) q
optRSel (RSel c1 (RSel c2 q))
  = RSel (SqlAnd c1 c2) (optRSel q)
-- σ c₁ (π l (σ c₂ q)) ≡ π l (σ (c₁ ∧ c₂) q)
-- discuss this with Eric?
optRSel (RSel c1 (RProj as (RSel c2 q)))
  = RProj as (RSel (SqlAnd c1 c2) (optRSel q))
  -- | noAttRename as = Proj as (Sel (VsqlAnd c1 c2) (optSel q))
  -- | otherwise      = q
  --   where
  --     noAttRename :: OptAttributes -> Bool
  --     noAttRename as = and $ fmap (isNothing . name . getObj) as
-- σ c (q₁ × q₂) ≡ q₁ ⋈\_c q₂
optRSel q@(RSel c (RProd q1 q2))
  | notInCond c = RJoin (optRSel q1) (optRSel q2) (relCond c)
  | otherwise   = q 
-- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_(c₁ ∧ c₂) q₂
optRSel q@(RSel c1 (RJoin q1 q2 c2))
  | notInCond c1 = RJoin q1 q2 (RAnd (relCond c1) c2)
  | otherwise    = q
-- optRSel (RSel c q)       = RSel c (optRSel q)
-- optRSel (RSetOp o q1 q2)  = RSetOp o (optRSel q1) (optRSel q2)
-- optRSel (RProj as q)     = RProj as (optRSel q)
-- optRSel (RJoin q1 q2 c) = RJoin (optRSel q1) (optRSel q2) c 
-- optRSel (RProd q1 q2)   = RProd (optRSel q1) (optRSel q2)
-- optRSel (RRenameAlg n q) = RRenameAlg n (optRSel q)
optRSel q                 = q

-- | recursive application of seldRDistr.
selRDistrRec :: RSchema -> RAlgebra -> RAlgebra
selRDistrRec s = transform (selRDistr s) 

-- | selection distributive properties.
selRDistr :: RSchema -> RAlgebra -> RAlgebra
selRDistr s q@(RSel (SqlAnd c1 c2) (RJoin q1 q2 c))
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₁ q₁) ⋈\_c (σ c₂ q₂)
  | check c1 t1 && check c2 t2 
    = RJoin (RSel c1 (selRDistr' q1))
            (RSel c2 (selRDistr' q2))
            c
  -- σ (c₁ ∧ c₂) (q₁ ⋈\_c q₂) ≡ (σ c₂ q₁) ⋈\_c (σ c₁ q₂)
  | check c2 t1 && check c1 t2 
    = RJoin (RSel c2 (selRDistr' q1)) 
            (RSel c1 (selRDistr' q2)) 
            c
  | otherwise = q 
    where 
      selRDistr' = selRDistr s 
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfRQuery q1 s 
      t2 = fromJust $ typeOfRQuery q2 s 
selRDistr s q@(RSel c1 (RJoin q1 q2 c2))
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ (σ c₁ q₁) ⋈\_c₂ q₂
  | check c1 t1
    = RJoin (RSel c1 (selRDistr s q1))
            (selRDistr s q2)
            c2
  -- σ c₁ (q₁ ⋈\_c₂ q₂) ≡ q₁ ⋈\_c₂ (σ c₁ q₂)
  | check c1 t2
    = RJoin (selRDistr s q1)
            (RSel c1 (selRDistr s q2))
            c2
  | otherwise = q 
    where
      check cond env = (not (notInCond cond) && inAttInEnv cond env)
                    || (notInCond cond && condAttsInEnv (relCond cond) env)
      t1 = fromJust $ typeOfRQuery q1 s 
      t2 = fromJust $ typeOfRQuery q2 s 
-- selRDistr (RSel c q)       s 
--   = RSel c (selRDistr q s)
-- selRDistr (RSetOp o q1 q2)  s 
--   = RSetOp o (selRDistr q1 s ) (selRDistr q2 s)
-- selRDistr (RProj as q)     s 
--   = RProj as (selRDistr q s)
-- selRDistr (RJoin q1 q2 c) s
--   = RJoin (selRDistr q1 s)
--           (selRDistr q2 s)
--           c 
-- selRDistr (RProd q1 q2)   s 
--   = RProd (selRDistr q1 s)
--           (selRDistr q2 s)
-- selRDistr (RRenameAlg n q) s = RRenameAlg n (selRDistr q s)
selRDistr _ q = q 

-- | gets a condition of the "IN" format and determines if
--   its attribute exists in a type env.
inAttInEnv :: SqlCond RAlgebra -> RTypeEnv -> Bool
inAttInEnv (SqlIn a _) t = attInEnv a t 
inAttInEnv _ _ = error "Can only accept conditions of the IN format!!"

-- | checks if an attribute exists in a type env or not.
attInEnv :: Attr -> RTypeEnv -> Bool
attInEnv a t = maybe False (\ _ -> True) (SM.lookup (attribute a) t)

-- | takes a relational condition and determines if it's 
--   consistent with a type env.
condAttsInEnv :: RCondition -> RTypeEnv -> Bool
condAttsInEnv (RLit _)        _ = True
condAttsInEnv (RComp _ a1 a2) t = case (a1, a2) of 
  (Val _, Att a)  -> attInEnv a t 
  (Att a, Val _)  -> attInEnv a t 
  (Att a, Att a') -> attInEnv a t && attInEnv a' t 
  _               -> True 
condAttsInEnv (RNot c)        t = condAttsInEnv c t 
condAttsInEnv (ROr c1 c2)     t = condAttsInEnv c1 t && condAttsInEnv c2 t 
condAttsInEnv (RAnd c1 c2)    t = condAttsInEnv c1 t && condAttsInEnv c2 t 

-- | recursive application of prjRDist.
-- prjRDistrRec :: RSchema -> RAlgebra -> RAlgebra
-- prjRDistrRec s = transform (prjRDistr s)

-- -- | projection distributive properties.
-- prjRDistr ::  RAlgebra -> RAlgebra
-- -- π (l₁, l₂) (q₁ ⋈\_c q₂) ≡ (π l₁ q₁) ⋈\_c (π l₂ q₂)
-- prjRDistr (RProj as (RJoin q1 q2 c)) = undefined
--   -- = RJoin (RProj as1 (prjDistr' q1))
--   --         (RProj as2 (prjDistr' q2))
--   --         c
--   --   where
--   --     t1  = fromJust $ typeOfRQuery (thing rq1) s 
--   --     pas = partitionAtts as (name rq1) t1
--   --     as1 = fst pas 
--   --     as2 = snd pas 
--   --     prjDistr' = flip prjRDistr s 
-- -- prjRDistr (RProj as q)     s 
-- --   = RProj as (prjRDistr q s)
-- -- prjRDistr (RSetOp o q1 q2)  s 
-- --   = RSetOp o (prjRDistr q1 s) (prjRDistr q2 s)
-- -- prjRDistr (RSel c q)       s 
-- --   = RSel c (prjRDistr q s)
-- -- prjRDistr (RJoin q1 q2 c) s 
-- --   = RJoin (prjRDistr q1 s)
-- --           (prjRDistr q2 s)
-- --           c
-- -- prjRDistr (RProd q1 q2)  s
-- --   = RProd (prjRDistr q1 s)
-- --           (prjRDistr q2 s)
-- -- prjRDistr (RRenameAlg n q) s = RRenameAlg n (prjRDistr q s)
-- prjRDistr q = q 
-- -- π (l₁, l₂) ((π (l₁, l₃) q₁) ⋈\_c (π (l₂, l₄) q₂)) ≡ π (l₁, l₂) (q₁ ⋈\_c q₂)
-- -- discuss with Eric. don't think we need this since we can regenerate
-- -- it with prjDistr and pushOutPrj

-- -- | partitions a list of attributes based on a given type env.
-- partitionAtts :: Attributes -> Alias -> RTypeEnv -> (Attributes, Attributes)
-- partitionAtts as n t = undefined
--   -- partition divideAtt as 
--   -- where
--   --   divideAtt :: Rename Attr -> Bool
--   --   divideAtt a = maybe False 
--   --                       (\inf -> maybe True
--   --                          (`elem` fmap rAttrQual inf) 
--   --                          ((qualifier . thing) a))
--   --                       (SM.lookup ((attribute . thing) a) t')
--   --   t' = updateType n t 








