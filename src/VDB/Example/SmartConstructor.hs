 -- | Example Queries upon an employee data base
module VDB.Example.SmartConstructor where

import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import Database.HDBC
import Prelude hiding (Ordering(..))

import VDB.Algebra
import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational

import qualified Data.Map as M 


--
--  ** smart contructor for plain query
--


plainAttr :: Attribute -> Opt Attribute 
plainAttr attrName = (F.Lit True, attrName)


plainAttrs :: [Attribute] -> [Opt Attribute]
plainAttrs []     = []
plainAttrs (x:xs) = plainAttr x : plainAttrs xs 


--
-- smart contructor for building schema 
--

-- | contruct plain Schema without tag assigned based on a list of [(Relatin Name, [Attribute name, Sqltype])] 
constructRelMap :: [(Relation, [(Attribute, SqlType)])] -> M.Map Relation (Opt RowType) 
constructRelMap nrlist = M.fromList $ map (\(relName, rt) -> ( relName, (Lit True, constructRowType relName rt))) nrlist

-- | contruct rowType based on a list of [(Attribute Name, SqlType)]


constructRowType ::  Relation -> [(Attribute,SqlType)]  -> RowType
constructRowType relName attrTypeList  = M.fromList  $ map (\(attrName, t) -> ( addRelToAtt attrName relName, (Lit True, t))) attrTypeList

