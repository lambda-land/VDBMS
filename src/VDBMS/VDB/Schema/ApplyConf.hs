-- | Variational database schema apply configuration operations.
module VDBMS.VDB.Schema.ApplyConf (

        appConfSchemaFexp,
        appConfSchema,
        appConfSchema',
        appConfSchemaStrct,
        appConfRowType,
        appConfRowType'

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Control.Arrow (first)

import VDBMS.VDB.Schema.Types
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Variational.Opt
import VDBMS.Features.Config (Config)

-- | apply config to fexp of schema.
appConfSchemaFexp :: Config Bool -> Schema -> Bool
-- appConfSchemaFexp c s = evalFeatureExpr c (featureModel s)
-- appConfSchemaFexp c s = evalFeatureExpr c $ featureModel s
appConfSchemaFexp c = evalFeatureExpr c . featureModel

-- | applies a config to a schema. Note that it keeps the 
--   attributes and relations that aren't valid in a variant
--   associated to the config.
appConfSchema :: Config Bool -> Schema -> Schema
appConfSchema c s 
  | schemaPres = (Lit (schemaPres), 
  M.map (appConfRowType c) (appConfSchemaStrct c $ schemaStrct s))
  | otherwise = error "the schema doesn't exist for the given config!"
  where 
    schemaPres = appConfSchemaFexp c s

-- | applies a config to a schema. Note that it filters out 
--   invalid objects. Note that the schema doesn't have pres cond
--   as one of the attributes of relations.
-- Note: the following must hold for all schemas:
-- appConfSchema' c5 employeeVSchema == appConfSchema' c5 empSchema5
appConfSchema' :: Config Bool -> Schema -> Schema
appConfSchema' c s = mkOpt (Lit $ appConfSchemaFexp c s) $
  (M.filter (\optRow -> getFexp optRow == Lit True) $ schemaStrct $ appConfSchema c s)

-- | applies a given config to the structure of the schema and 
--   drops the tables that aren't valid.
appConfSchemaStrct :: Config Bool -> Map Relation TableSchema -> Map Relation TableSchema
appConfSchemaStrct c s = M.filter (\r -> if getFexp r == Lit True then True else False) s'
  where s' = M.map (appConfRowType' c) s


-- | apply config to a rowtype. it doesn't filter out invalid attributes.
appConfRowType :: Config Bool -> TableSchema -> TableSchema
appConfRowType c (f,r) = mkOpt (Lit (evalFeatureExpr c f)) $
  M.map (first $ Lit . evalFeatureExpr c) r
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 

-- | apply config to a rowtype. it filters out invalid attributes.
appConfRowType' :: Config Bool -> TableSchema -> TableSchema
appConfRowType' c r = updateOptObj (M.filter 
  (\optType -> getFexp optType == Lit True) $ getObj r') r'
    where r' = appConfRowType c r
  -- (Lit (evalFeatureExpr c f),
  -- M.map (first $ Lit . evalFeatureExpr c) r)
--  M.map (\(f,t) -> (Lit (evalFeatureExpr c f),t)) r 

