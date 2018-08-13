module VDB.TypeSystem.Semantics where 

import VDB.Algebra 
import Prelude hiding (EQ,LT , GT)
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import VDB.Variational
import VDB.Value  
import VDB.Schema
import VDB.Config 


import Data.Map(Map)
import qualified Data.Map as Map 

import Control.Monad.State
import Control.Monad (liftM2)

 


import Data.Set(Set) 
import qualified Data.Set as Set 

-- import Data.Maybe(catMaybes)

-- 
-- * dynamic semantics of variational objects:
--

-- | semantics of variational attributes
semOptAttr :: [Opt Attribute] -> Config Bool -> [Attribute]
semOptAttr []              _ = []
semOptAttr as        c = configureOptList c as 

-- | semantics of variational relation
semOptRel :: Opt RowType -> Config Bool -> [(Attribute, Type)]
semOptRel vrel c = case configureOpt c vrel of 
                      Nothing -> []
                      Just rowList -> configureOptList c rowList

-- | semantics of variational Schema
semVsch :: Schema -> Config Bool -> (Map Relation [(Attribute, Type)])
semVsch s@(_,m)  c = case Map.null m of 
                         True  -> Map.empty
                         _     -> case configureOpt c s of 
                                Just m ->  Map.map ((flip semOptRel) c) m
                                Nothing -> Map.empty 

-- | Traverse the Map and collect the Just results.
traverseRelMap :: Map Relation (Maybe RowType) -> Map Relation RowType 
traverseRelMap relM = Map.mapMaybe (\v -> v) relM   


--
-- * Variational Relational Algebra Validation Semantics / Type System
--



-- | type enviroment is a mapping from variational objects to their presence conditions
-- data Env a = Map Objects a 




-- type Schema = Opt (Map Relation (Opt RowType))
-- type RowType = [Opt (Attribute,Type)]

type RowTypeP = [(Attribute, Type)]
type SchemaP = Map Relation RowTypeP

data Objects = TAttr Attribute 
             | TRel  Relation
             | TSch  SchemaP
             deriving (Show, Eq,Ord)


-- | s: a mapping from objects to presence condition (featureExpr)
-- | result: presence condition (featureExpr)
type Env = StateT (Map Objects F.FeatureExpr) Maybe 


-- | static semantics for V-conditions
semVcond :: C.Condition -> Env Schema 
semVcond (C.Lit b)             = undefined
semVcond (C.Comp op a1 a2)     = undefined 
semVcond (C.Not  cond)         = undefined
semVcond (C.Or   cond1 cond2)  = undefined
semVcond (C.And  cond1 cond2)  = undefined
semVcond (C.CChc _ _ _ )       = undefined

-- | static semantics for V-query
semVquery :: Algebra -> Env Schema
semVquery  (AChc  f l r)       = undefined
semVquery  (SetOp Prod l r)    = undefined 
semVquery  (SetOp Union l r)   = undefined
semVquery  (SetOp Diff l r)    = undefined
semVquery  (Proj  opAttrs a)   = do st <- get
                                    let newAList = map (\(f,a) ->  (TAttr a,f)) opAttrs
                                    let newMap = Map.fromList newAList
                                    put $ Map.union st newMap 
                                    semVquery a
semVquery  (Sel   cond a)      = do st <- get
                                    
semVquery  (TRef  r)           = undefined
semVquery   Empty              = undefined









