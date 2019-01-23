-- Sends queries from the relational translation to the db 
-- and gets the plain relational result
module VDB.NaiveApproach.NaiveSendQs where 

import VDB.Translations.RelAlg2Sql (Query,VariantQuery)
import VDB.Variant (Variant)
import VDB.SqlTable

-- import Data.Text as T (Text, pack, append, concat, unpack)
-- import Data.Map

import Database.HDBC

--prepare :: conn -> String -> IO Statement
-- | constructs a statement (i.e. the datatype for query acceptable by
--   HDBC) from a query
mkStatement :: IConnection conn => Query -> conn -> IO Statement
--mkStatement q conn = prepare conn q
mkStatement  = flip prepare 


-- fetchAllRowsMap :: Statement -> IO [Map String SqlValue]
-- | gets a VariantQuery and returns the result
--  with the configuration attached to it.
runNaiveQ :: IConnection conn => VariantQuery -> conn -> IO SqlVariantTable
runNaiveQ (e,v) conn = do 
  q <- mkStatement e conn
  r <- fetchAllRowsMap q 
  return (r,v)

-- | gets a list of VariantQueries
--  and returns their results with theri config attached.
runNaiveQs :: IConnection conn => [VariantQuery] -> conn -> IO [SqlVariantTable]
runNaiveQs qs conn = mapM ((flip runNaiveQ) conn) qs

