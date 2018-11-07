-- Sends queries from the brute force translation to the db 
-- and gets the plain relational result
module VDB.BruteForce.BruteForceSendQs where 

--import Prelude hiding (EQ ,LT ,GT)
-- import VDB.SQL 
import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C
import qualified VDB.Target as T
import VDB.Variational
import VDB.Value  
--import VDB.BruteForce.BruteForceAlg2Sql
--import VDB.DBsetup.EnronEmailDB

import Control.Monad

import Data.Text as T (Text, pack, append, concat, unpack)
import Data.Map

--import Database.HDBC.Sqlite3
import Database.HDBC


type Row = [SqlValue]
type Table = [Row]
type Vtable = Opt Table

type ClmNameIncludedRow = [(String, SqlValue)]
type ClmNameIncludedTable = [ClmNameIncludedRow]
type ClmNameIncludedVtable = Opt ClmNameIncludedTable

type ClmRowMap = Map String SqlValue
type ClmTableMap = [ClmRowMap]
type ClmVtableMap = Opt ClmTableMap

type Query = T.Text
type Vquery = Opt Query

--prepare :: conn -> String -> IO Statement
-- | constructs a statement (i.e. the datatype for query acceptable by
--   HDBC) from a query
mkStatement :: IConnection conn => Query -> conn -> IO Statement
--mkStatement t conn = prepare conn (T.unpack t)
mkStatement  = flip prepare . T.unpack


--mkOptStmt :: IConnection conn => Vquery -> conn -> IO (Opt Statement)
--mkOptStmt (o,t) conn = do 
--  s <- prepare conn (T.unpack t)
--  return (o,s)

-- fetchAllRows :: Statement -> IO [[SqlValue]]
-- | gets a query with its assigned fexp and returns the result
--  with the table pres cond attached to it
runBruteQ :: IConnection conn => Vquery -> conn -> IO Vtable
runBruteQ (o,t) conn = do 
  q <- mkStatement t conn
  r <- fetchAllRows q 
  return (o,r)

-- | gets a list of queries with their assigned fexp
--  and returns their results with the table pres cond
runBruteQs :: IConnection conn => [Vquery] -> conn -> IO [Vtable]
runBruteQs qs conn = mapM ((flip runBruteQ) conn) qs

-- fetchAllRowsAL :: Statement -> IO [[(String, SqlValue)]]
-- | gets a vquery and returns a vtable where column names are included
runBruteQclm :: IConnection conn => Vquery -> conn -> IO ClmNameIncludedVtable
runBruteQclm (o,t) conn = do
  q <- mkStatement t conn
  r <- fetchAllRowsAL q
  return (o,r)


-- | gets a list of vqueries and returns a vtable where column names 
--   are included
runBruteQsClm :: IConnection conn => [Vquery] -> conn -> IO [ClmNameIncludedVtable]
runBruteQsClm qs conn = mapM ((flip runBruteQclm) conn) qs

-- fetchAllRowsMap :: Statement -> IO [Map String SqlValue]
-- | gets a vquery and returns a table where each row is a map of 
--   attribute name to value (might be more efficient! double check
--   with Eric)
runBruteQclmMap :: IConnection conn => Vquery -> conn -> IO ClmVtableMap
runBruteQclmMap (o,t) conn = do
  q <- mkStatement t conn
  r <- fetchAllRowsMap q
  return (o,r)

runBruteQsClmMap :: IConnection conn => [Vquery] -> conn -> IO [ClmVtableMap]
runBruteQsClmMap qs conn = mapM ((flip runBruteQclmMap) conn) qs

