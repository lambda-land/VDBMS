-- | Representation of tuples and tables for interpreting variational queries.
module VDBMS.VDB.Database where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as Set
import Data.SBV (Boolean)
import Data.List (intercalate)
import Data.Bitraversable
import Data.Bifunctor
import Data.Maybe
import Data.Text as T (Text, unpack)
import Data.Convertible 
-- (safeConvert)

import Control.Monad (zipWithM)

import VDBMS.QueryTrans.RelAlg2Sql (VariantQuery)
import VDBMS.Features.FeatureExpr
import VDBMS.VDB.Name
import VDBMS.Features.SAT
import VDBMS.VDB.Schema
import VDBMS.Features.Variational
import VDBMS.DBMS.Type
import VDBMS.VDB.Table
import VDBMS.DBMS.SqlTable 
import VDBMS.Features.Variant
import VDBMS.Features.Config

import Database.HDBC 
import Database.HDBC.Sqlite3 
-- import Database.HDBC.Types

-- | sqldatabase. either a variational database or a variant of a VDB.
--   note that the relations, attributes, and tuples have been filtered
--   out of a variant if they're not valid for that variant. 
--   @Eric: do I need to keep the IConnection constraint?!?!?!
data SqlDatabase conn where 
  VariantDB :: IConnection conn => Schema -> Variant conn Bool -> SqlDatabase conn 
  VDB       :: IConnection conn => Schema -> conn -> SqlDatabase conn 
  -- deriving (Eq)


getSqlDBschema :: IConnection conn => SqlDatabase conn -> Schema
getSqlDBschema (VariantDB s _) = s 
getSqlDBschema (VDB s _)       = s

getSqlData :: IConnection conn => SqlDatabase conn -> conn
getSqlData (VariantDB _ v) = getVariant v
getSqlData (VDB _ c)       = c

-- | gets a configuration of a variant from a sqldatbase.
--   note: the db isn't variational
getSqlConfig :: IConnection conn => SqlDatabase conn -> Config Bool
getSqlConfig (VariantDB _ v) = getConfig v 
getSqlConfig _               = error "cannot get config of a variational db!"

-- | generates the valid configurations of a variational database.
getAllConfig :: IConnection conn => SqlDatabase conn -> [Config Bool]
getAllConfig (VDB s _ ) = validConfsOfFexp $ featureModel s
getAllConfig _          = error "cannot get all variant configurations from a db!"

type DBFilePath = String

-- ****************DON'T ERASE***********************************************
-- | gets the physical path where the db is stored.
--   TODO: write this function!!
-- getSqlDBpath :: IConnection conn => SqlDatabase conn -> FilePath
-- getSqlDBpath (VariantDB _ v ) = case conn of 
--                                        co
-- getSqlDBpath (VDB _ c) 
--   where 
--     conn = getVariant v 

-------------------------- running/constructing queries on sqldatabase---------------

type QueryString = String 

type Query = IO Statement

-- | constructs a query from text.
mkStatement :: IConnection conn => SqlDatabase conn -> QueryString -> Query
mkStatement db q = prepare (getSqlData db) q

-- | helper func for configVDB. returns a list of valid tables in a variant.
validRels :: Config Bool -> Schema -> [Relation]
validRels c s = Set.toList $ getRels vs 
  where 
    vs = appConfSchema' c s 

-- | returns a set of valid attributes for a relation in a given config 
--   of a vdb.
validAtts :: Config Bool -> Relation -> Schema -> Set Attribute 
validAtts c r s = case rowType of 
        Just atts -> getRowTypeAtts atts
        _         -> Set.empty
  where 
    rowType = lookupRel r $ appConfSchema' c s

-- | drops the pres cond from valid atts.
-- DANGER: changed Attribute to (Attribute (Just r))
-- MAY CAUSE PROBLEMS!!!
validAttsWithoutPres :: PresCondAtt -> Config Bool -> Relation -> Schema -> Set Attribute 
validAttsWithoutPres p c r s = Set.delete (Attribute (Just r) $ presCondAttName p) $ validAtts c r s

-------------------- run variational queries for approach1 -------------------------------
type QueryText = T.Text

type TranslatedVquery = Opt QueryText

-- | runs a translated query from vquery on the vdb.
--   Note that a vq translates to a list of opt query.
runTransQ :: IConnection conn => TranslatedVquery -> SqlDatabase conn -> IO SqlVtable 
runTransQ q db = do
  stmt <- mkStatement db $ T.unpack $ getObj q
  _ <- execute stmt []
  r <- fetchAllRowsMap' stmt 
  return $ mkOpt (getFexp q) r


-- | runs the translated list of queries of a vquery on the vdb.
runVq :: IConnection conn => [TranslatedVquery] -> SqlDatabase conn -> IO [SqlVtable]
runVq qs db = mapM (flip runTransQ db) qs
  


-------------------- run variant queries for brute force -------------------------------

-- | runs a query related only to one variant on a variational db.
runSqlQ :: IConnection conn => Config Bool -> QueryString -> SqlDatabase conn -> IO SqlVariantTable
runSqlQ c t db = do 
  q <- mkStatement db t 
  _ <- execute q []
  r <- fetchAllRowsMap' q
  return $ mkVariant r c

-- | runs a list of queries related only to a variant on a variational db.
runSqlQs :: IConnection conn => Config Bool -> [QueryString] -> SqlDatabase conn -> IO [SqlVariantTable]
runSqlQs c ts db = mapM ((flip $ runSqlQ c) db) ts

-- | runs a variant query on a variant db if their config are equal over the schema fexp.
runVariantSqlOnVariantDB :: VariantQuery -> SqlDatabase Connection -> IO (Maybe SqlVariantTable)
runVariantSqlOnVariantDB q db = do 
  let qConf = getConfig q 
      dbConf = getSqlConfig db
      qText = getVariant q
      b = equivConfigOnSchema (getSqlDBschema db) qConf dbConf
  res <- runSqlQ dbConf qText db
  -- commit $ getSqlData db
  disconnect $ getSqlData db
  return $ if b then Just res else Nothing

-- | runs a list of variant queries on a list of variant sqldbs. i.e. it runs a query
--   on its correspondent db.
runSqlQsOnCorrespDBs :: [VariantQuery] -> [SqlDatabase Connection] -> IO [SqlVariantTable]
runSqlQsOnCorrespDBs qs dbs = do 
  res <- zipWithM runVariantSqlOnVariantDB qs dbs
  return $ catMaybes res
  
-------------------- configre a variational db (for brute force) --------------------
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
genCreateQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [QueryString]
genCreateQs p c vdb = do 
  let validSchema    = appConfSchema' c (getSqlDBschema vdb)
      validRelations = validRels c (validSchema)
  qs <- mapM (flip (genTableDesc p c) vdb) validRelations 
  return qs

-- | gets attributes of a table and their type to regenerate 
--   create queries for a specific variant. helper for genCreateQs.
-- NOTE: takes the first tuple and gets the type of attribute from that,
--       if the first tuple has a real null value it messes the whole thing up!
genTableDesc :: IConnection conn => PresCondAtt -> Config Bool -> Relation -> SqlDatabase conn -> IO String
genTableDesc p c r vdb = do 
  tableDesc <- describeRelWithoutPres p c vdb r
  let attDesc a = fst a ++ " " ++ hdbcType2SqlType (colType (snd a)) 
      desc = fmap attDesc tableDesc
  return $ "create table " ++ relationName r ++ "( " ++ intercalate ", " desc ++ ");"

-- | running create queries. Note the sqldatabase is a variant database and NOT 
--   a variational table.
-- runCreateQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> conn -> IO Integer
-- runCreateQs p c vdb conn = genCreateQs p c vdb >>= \x -> run conn x []

runCreateQs' :: IConnection conn => [QueryString] -> conn -> IO ()
runCreateQs' qs conn = do
  -- genCreateQs p c vdb >>= 
  mapM (flip (run conn) []) qs 
  commit conn

-- | returns a list of attributes to be projected for the genSelectQs.
--   note: it INCLUDES pres cond attribute. 
attList :: IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> String
attList c vdb r = intercalate ", " validAtt
  where 
    -- validSchema = appConfSchema' c $ getSqlDBschema vdb
    validAtt    = Set.toList $ Set.map attributeName $ validAtts c r $ getSqlDBschema vdb

-- | generates a select query for a relation to copy it for a specific config of vdb.
genSelectQ ::  IConnection conn => Config Bool -> PresCondAtt -> SqlDatabase conn -> Relation -> QueryString
genSelectQ c p vdb r = select ++ atts ++ from ++ relationName r
  where 
    select = "select " 
    from   = " from "
    atts   = attList c vdb r ++ ", " ++ presCondAttName p 

-- | helper func for configVDB. generates queries to get all
--   data from a vdb w.r.t. a config.
genSelectQs :: IConnection conn => Config Bool -> PresCondAtt -> SqlDatabase conn -> [(Relation,QueryString)]
genSelectQs c p vdb = zip rels $ map (++ ";") $ map (genSelectQ c p vdb) rels
  where
    rels = validRels c (getSqlDBschema vdb)

-- | runs a selection query. note that after running the select queries
--   you need to filter tuples s.t. the ones with false pres cond are omitted.
--   dropRows does this. from there you need to drop the pres conds. 
--   dropPres does this.
runSelectQ :: IConnection conn => SqlDatabase conn -> (Relation,QueryString) -> IO (Relation,SqlTable)
runSelectQ vdb (r,q) = do 
  stmt <- mkStatement vdb q
  _ <- execute stmt []
  table <- fetchAllRowsMap' stmt
  return $ (,) r table 

-- | preps the result of a select query for insertion query.
--   applies a config, filters tuples with false pres cond and then drops pres conds completely.
prepForInsertQ :: PresCondAtt -> Schema -> Config Bool -> (Relation,SqlTable) -> (Relation,SqlTable)
prepForInsertQ p s c (r,t) = (r,dropPresInTable p $ dropRows p t')
  -- (r,dropRows p t')
  where 
    as = validAtts c r s 
    t' = applyConfTable c as p t

-- | returns the relations and their tuples to be inserted. 
insertionVals :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [(Relation,SqlTable)]
insertionVals p c vdb = do 
  let rqs = genSelectQs c p vdb
  initialVals <- mapM (runSelectQ vdb) rqs -- [(r,t)]
  return $ fmap (prepForInsertQ p (getSqlDBschema vdb) c) initialVals


-- | generates all insert queries for a specific config.
genInsertQs' :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [QueryString]
genInsertQs' p c vdb = do 
  tables <- insertionVals p c vdb
  return $ fmap (genInsertQ' c $ getSqlDBschema vdb) tables

-- | generates insert queries for a specific config for one relation.
genInsertQ' :: Config Bool -> Schema -> (Relation, SqlTable) -> QueryString
genInsertQ' c vdb_s (r,t) = "insert into " ++ rName ++ " (" ++ clms ++ ") values " ++ vals ++ ";"
  where 
    rName  = relationName r
    attsList = Set.toAscList $ validAtts c r vdb_s
    clms = intercalate ", " $ map attributeName attsList
    vals = intercalate ", " $ map (genValsRowComplyAttList attsList) t

-- | generates values of a sqlrow based on a list of attributes for insertion Q.
-- NOTE: it's problematic for null values!!
-- TODO: refactor for null!!
genValsRowComplyAttList :: [Attribute] -> SqlRow -> QueryString
genValsRowComplyAttList l r
  | attNameList == M.keys r = "( " ++ intercalate ", " (map (++ "'") $ map ("'" ++) $ map safeConvert' $ M.elems r) ++ " )"
  | otherwise = error "couldn't comply the sqlrow to attribute list while gen vals for insertion!"
    where
      attNameList = map attributeName l 
      -- safeConvert' :: SqlValue -> String
      safeConvert' v = case safeFromSql v of 
                         Right val -> val 
                         Left (ConvertError sval stype dtype err)        -> error ("!!!!" ++ sval ++ stype ++ dtype ++ err)
                         -- error "cannot convert sqlvalue to srting in gen insertion queries!"
    
-- | runs generated insertion qs to insert values into a configured db.
runInsertQs' :: IConnection conn => [QueryString] -> conn -> IO ()
runInsertQs' = runCreateQs'

{- OLD VERSION THAT DIDN'T WORK. READ THE NOTE!!!!
-- | helper func for configVDB. generates insert queries for a specific config.
-- NOTE: I cannot use this function since hdbc sends it directly to sqlite instead
--       of prepping queries and then sending them with values.
genInsertQ :: IConnection conn => Config Bool -> SqlDatabase conn -> Relation -> QueryString
genInsertQ c vdb r = "insert into " ++ rName ++ " (" ++ qMarks ++ ")"
  where 
    rName  = relationName r
    qMarks = intercalate "," $ replicate (n) "?"
    validSchema = appConfSchema' c $ getSqlDBschema vdb
    n      = relArity r validSchema

-- | generates insertion queries and pairs them up with their values.
genInsertQs :: IConnection conn => PresCondAtt -> Config Bool -> SqlDatabase conn -> IO [(QueryString,[[SqlValue]])]
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

runInsertQs' :: IConnection conn => [(QueryString,[[SqlValue]])] -> conn -> IO ()
runInsertQs' qts conn =  do 
  -- qts <- genInsertQs p c vdb
  let stmt q = prepare conn q
  res <- mapM (bitraverse stmt pure) qts
  mapM_ (\(iq,t) -> executeMany iq t) res
  commit conn

-}

-- | creates a variant db from the provided config and vdb.
--   TODO: it doesn't work with the type constraint: IConnection conn =>
--         figure out the problem!!!
configVDB ::  DBFilePath -> PresCondAtt -> SqlDatabase Connection 
  -> Config Bool -> Int -> IO (SqlDatabase Connection)
configVDB f p vdb c i = do
  let vdb_schema = getSqlDBschema vdb
      db_schema = appConfSchema' c vdb_schema
  createQs <- genCreateQs p c vdb 
  -- insertQs <- genInsertQs p c vdb
  insertQs <- genInsertQs' p c vdb 
  -- disconnect $ getSqlData vdb
  conn <- connectSqlite3 $ f ++ show i ++ ".db"
  runCreateQs' createQs conn 
  runInsertQs' insertQs conn
  disconnect conn
  return $ VariantDB db_schema $ mkVariant conn c 


-- | creates a list of variant dbs from a list of configs for a vdb.
--   Note that this should be done for all configs that satisfy the
--   fexp of vschema. however we're providing the list of configs 
--   manuall for now. 
--   TODO: get the list of valid configs from the vschema fexp instead
--         of passing the list of config to this func.
--   TODO: type constraint problem!!!! kmn IConnection conn =>
configVDBall ::  DBFilePath -> PresCondAtt -> SqlDatabase Connection 
                 -> [Config Bool] -> IO [SqlDatabase Connection]
configVDBall f p vdb cs = do
  -- let nums = [1..length cs]
  sequence $ zipWith (configVDB f p vdb) cs [1..]



