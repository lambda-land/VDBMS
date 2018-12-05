-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForceSendQs where 

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
import VDB.BruteForce.BruteForceAlg2Sql (Query,VariantQuery)
import VDB.Config (Variant)

import Control.Monad

-- import Data.Text as T (Text, pack, append, concat, unpack)
import Data.Map

import Database.HDBC

-- type Row = [SqlValue]
-- type Table = [Row]
-- type Vtable = Opt Table

-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type ClmNameIncludedVariantTable = Variant Bool ClmNameIncludedTable
-- type ClmNameIncludedVtable = Opt ClmNameIncludedTable

type ClmRowMap = Map String SqlValue
type ClmTableMap = [ClmRowMap]
type ClmVariantTableMap = Variant Bool ClmTableMap
-- type ClmVtableMap = Opt ClmTableMap


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

