-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForceSendQs where 

import VDB.BruteForce.BruteForceAlg2Sql (Query,VariantQuery)
import VDB.Variant (Variant)
import VDB.SqlTable

-- import Data.Text as T (Text, pack, append, concat, unpack)
import Data.Map

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
runBruteQ :: IConnection conn => VariantQuery -> conn -> IO ClmVariantTableMap
runBruteQ (v,e) conn = do 
  q <- mkStatement e conn
  r <- fetchAllRowsMap q 
  return (v,r)

-- | gets a list of VariantQueries
--  and returns their results with theri config attached.
runBruteQs :: IConnection conn => [VariantQuery] -> conn -> IO [ClmVariantTableMap]
runBruteQs qs conn = mapM ((flip runBruteQ) conn) qs

