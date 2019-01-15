-- | Representation of tuples and tables for interpreting variational queries.
module VDB.Database where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as Set
import Data.SBV (Boolean)
import Data.List (intercalate)
import Data.Bitraversable
import Data.Bifunctor

import VDB.FeatureExpr
import VDB.Name
import VDB.SAT
import VDB.Schema
import VDB.Variational
import VDB.Type
import VDB.Table
import VDB.SqlTable 
import VDB.Variant
import VDB.Config

import Database.HDBC 
-- import Database.HDBC.Sqlite3 (Connection)

-- | sqldatabase. either a variational database or a variant of a VDB.
--   note that the relations, attributes, and tuples have been filtered
--   out of a variant if they're not valid for that variant. 
--   @Eric: do I need to keep the IConnection constraint?!?!?!
data SqlDatabase conn where 
  VariantDB :: IConnection conn => Schema -> Variant conn Bool -> SqlDatabase conn 
  VDB       :: IConnection conn => Schema -> conn -> SqlDatabase conn 

getSqlDBschema :: SqlDatabase conn -> Schema
getSqlDBschema (VariantDB s _) = s 
getSqlDBschema (VDB s _)       = s

getSqlData :: SqlDatabase conn -> conn
getSqlData (VariantDB _ v) = getVariant v
getSqlData (VDB _ c)       = c

-- | gets a configuration of a variant from a sqldatbase.
--   note: the db isn't variational
getSqlConfig :: SqlDatabase conn -> Config Bool
getSqlConfig (VariantDB _ v) = getConfig v 
getSqlConfig _               = error "cannot get config of a variational db!"

-- TODO: you can later on return all the config 
--       that vdb is valid for in the second case
getAllConfig :: SqlDatabase conn -> [Config Bool]
getAllConfig (VDB s _ ) = undefined
getAllConfig _          = error "cannot get all variant configurations from a db!"

type QueryText = String 

type Query = IO Statement

-- | constructs a query from text.
mkStatement :: IConnection conn => SqlDatabase conn -> QueryText -> Query
mkStatement db q = prepare (getSqlData db) q

-- | helper func for configVDB. returns a list of valid tables in a variant.
validRels :: Config Bool -> Schema -> [Relation]
validRels c s = Set.toList $ getRels vs 
  where 
    vs = appConfSchema c s 

-- | returns a set of valid attributes for a relation in a given config 
--   of a vdb.
validAtts :: Config Bool -> Relation -> Schema -> Set Attribute 
validAtts c r s = case rowType of 
        Just atts -> getRowTypeAtts atts
        _         -> Set.empty
  where 
    rowType = lookupRel r s

-- | drops the pres cond from valid atts.
validAttsWithoutPres :: PresCondAtt -> Config Bool -> Relation -> Schema -> Set Attribute 
validAttsWithoutPres p c r s = Set.delete (Attribute $ presCondAttName p) $ validAtts c r s

-- | runs a query related only to one variant on a variational db.
runSqlQ :: IConnection conn => Config Bool -> QueryText -> SqlDatabase conn -> IO SqlVariantTable
runSqlQ c t db = do 
  q <- mkStatement db t 
  r <- fetchAllRowsMap' q
  return $ mkVariant r c

-- | runs a list of queries related only to a variant on a variational db.
runSqlQs :: IConnection conn => Config Bool -> [QueryText] -> SqlDatabase conn -> IO [SqlVariantTable]
runSqlQs c ts db = mapM ((flip $ runSqlQ c) db) ts

{- -- MAY COME HANDY. DON'T DELETE!!
-- | describes a relation from a vdb for a specific variant. i.e.
--   it returns a list of attribute that are present in the schema
--   of the given variant.
-- TODO: instead of string return attribute.
describeRelation :: IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> IO [(String, SqlColDesc)]
describeRelation c vdb r = do 
  let sqlData     = getSqlData vdb
      validSchema = appConfSchema' c $ getSqlDBschema vdb
      validAtt    = Set.map attributeName $ validAtts c r validSchema
      -- rowType = lookupRel r validSchema
      -- validAtt = case rowType of 
      --   Just atts -> Set.map attributeName $ getRowTypeAtts atts
      --   _ -> Set.empty
  as <- describeTable sqlData $ relationName r
  return $ filter (\(a,_) -> Set.member a validAtt) as
-}
  
-- | drops the pres cond from relation description.
describeRelWithoutPres :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> Relation -> IO [(String, SqlColDesc)]
describeRelWithoutPres p c vdb r = do 
  let sqlData     = getSqlData vdb
      validSchema = appConfSchema' c $ getSqlDBschema vdb
      validAtt    = Set.map attributeName $ validAttsWithoutPres p c r validSchema
  as <- describeTable sqlData $ relationName r
  return $ filter (\(a,_) -> Set.member a validAtt) as

-- | generates create queries.
--   concat all queries and send them once using the "runRaw" func.
-- the sqldb is variational
genCreateQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO QueryText
genCreateQs p c vdb = do 
  let validSchema    = appConfSchema' c (getSqlDBschema vdb)
      validRelations = validRels c (validSchema)
  qs <- mapM (flip (genTableDesc p c) vdb) validRelations 
  return $ concat qs 

-- | gets attributes of a table and their type to regenerate 
--   create queries for a specific variant. helper for genCreateQs
genTableDesc :: IConnection conn => PresCondAtt -> Config Bool -> Relation -> SqlDatabase conn -> IO String
genTableDesc p c r vdb = do 
  tableDesc <- describeRelWithoutPres p c vdb r
  let attDesc a = fst a ++ " " ++ hdbcType2SqlType (colType (snd a)) 
      desc = fmap attDesc tableDesc
  return $ "create table " ++ relationName r ++ "( " ++ intercalate ", " desc ++ ");"

-- | running create queries. Note the sqldatabase is a variant database and NOT 
--   a variational table.
runCreateQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> conn -> IO Integer
runCreateQs p c vdb conn = genCreateQs p c vdb >>= \x -> run conn x []

-- | returns a list of attributes to be projected for the genSelectQs.
--   note: it INCLUDES pres cond attribute. 
attList :: IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> String
attList c vdb r = intercalate ", " validAtt
  where 
    validSchema = appConfSchema' c $ getSqlDBschema vdb
    validAtt    = Set.toList $ Set.map attributeName $ validAtts c r validSchema

-- | generates a select query for a relation to copy it for a specific config of vdb.
genSelectQ ::  IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> QueryText
genSelectQ c vdb r = select ++ atts ++ from ++ relationName r
  where 
    select = "select " 
    from   = " from "
    atts   = attList c vdb r 

-- | helper func for configVDB. generates queries to get all
--   data from a vdb w.r.t. a config.
genSelectQs :: IConnection conn => Config Bool -> SqlDatabase conn -> [(Relation,QueryText)]
genSelectQs c vdb = zip rels $ map (++ ";") $ map (genSelectQ c vdb) rels
  where
    rels = validRels c (getSqlDBschema vdb)

-- | runs a selection query. note that after running the select queries
--   you need to filter tuples s.t. the ones with false pres cond are omitted.
--   dropRows does this. from there you need to drop the pres conds. 
--   dropPres does this.
runSelectQ :: IConnection conn => SqlDatabase conn -> (Relation,QueryText) -> IO (Relation,SqlTable)
runSelectQ vdb (r,q) = do 
  stmt <- mkStatement vdb q
  table <- fetchAllRowsMap' stmt
  return $ (,) r table 

-- | preps the result of a select query for insertion query.
--   filters tuples with false pres cond and then drops pres conds completely.
prepForInsertQ :: PresCondAtt -> (Relation,SqlTable) -> (Relation,SqlTable)
prepForInsertQ p (r,t) = (r,dropPresInTable p $ dropRows p t)


-- | returns the relations and their tuples to be inserted. 
insertionVals :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [(Relation,SqlTable)]
insertionVals p c vdb = do 
  let rqs = genSelectQs c vdb
  initialVals <- mapM (runSelectQ vdb) rqs
  return $ fmap (prepForInsertQ p) initialVals

-- | helper func for configVDB. generates insert queries for a specific config.
genInsertQ :: IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> QueryText
genInsertQ c vdb r = "insert into " ++ rName ++ " ( " ++ qMarks ++ " )"
  where 
    rName  = relationName r
    qMarks = intercalate "," $ replicate (n) "?"
    validSchema = appConfSchema' c $ getSqlDBschema vdb
    n      = relArity r validSchema

-- | generates insertion queries and pairs them up with their values.
genInsertQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [(QueryText,[[SqlValue]])]
genInsertQs p c vdb = do
  tables <- insertionVals p c vdb
  return $ fmap (bimap (genInsertQ c vdb) genSqlVals) tables

-- | creates [[sqlvalue]] from sqltable.
genSqlVals :: SqlTable -> [[SqlValue]]
genSqlVals = fmap M.elems 

-- | runs the instertion queries with their values. i.e. generates the new
--   vdb.
runInsertQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> conn -> IO ()
runInsertQs p c vdb conn =  do 
  qts <- genInsertQs p c vdb
  let stmt q = prepare conn q
  res <- mapM (bitraverse stmt pure) qts
  mapM_ (\(iq,t) -> executeMany iq t) res

-- | creates a variant db from the provided config and vdb.
configVDB :: IConnection conn => PresCondAtt -> Config Bool -> conn -> SqlDatabase conn -> IO (SqlDatabase conn)
configVDB p c conn vdb = do
  let vdb_schema = getSqlDBschema vdb
      db_schema = appConfSchema' c vdb_schema
  runCreateQs p c vdb conn 
  runInsertQs p c vdb conn
  return $ VariantDB db_schema $ mkVariant conn c 



