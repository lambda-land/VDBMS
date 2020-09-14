-- | Tables returned by HDBC.
module VDBMS.DBMS.Table.Table (

        SqlRow,
        SqlTable,
        rowAttSet,
        tableAttSet,
        constRowTypeOfSqlTable,
        insertAttValToSqlTable,
        conformSqlRowToRowType,
        dropPresInTable,
        applyConfTable,
        applyConfTables,
        dropRows,
        dropUnsatTuples,
        combineSqlTables,
        updatePCInSqlTable,
        conformSqlTableToSchema,
        lookupAttValInSqlRow, 
        ppSqlTable

) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Maybe (fromJust, isNothing)

import VDBMS.Features.SAT (satisfiable)
import VDBMS.VDB.Name
import VDBMS.Features.Config
import VDBMS.Features.FeatureExpr.FeatureExpr
import VDBMS.VDB.Schema.Variational.Schema
import VDBMS.DBMS.Value.Value

import Database.HDBC (SqlValue(..))

import Control.Monad.Catch
import Data.Data (Data, Typeable)
import GHC.Generics (Generic)

import Text.PrettyPrint.Boxes

-- type Row = [SqlValue]
-- type Table = [Row]
-- type Vtable = Opt Table

-- type ClmNameIncludedRow = [(String, SqlValue)]
-- type ClmNameIncludedTable = [ClmNameIncludedRow]
-- type ClmNameIncludedVariantTable = Variant ClmNameIncludedTable Bool
-- type ClmNameIncludedVtable = Opt ClmNameIncludedTable

-- type ClmRowMap = Map String SqlValue
-- type ClmTableMap = [ClmRowMap]
-- type ClmVariantTableMap = Variant ClmTableMap Bool
-- type ClmVtableMap = Opt ClmTableMap

type SqlRow = Map String SqlValue
type SqlTable = [SqlRow]

data SqlTableErr
  = AttNotInRow Attribute Relation SqlRow
  deriving (Data,Eq,Generic,Ord,Show,Typeable)

instance Exception SqlTableErr

-- |prints a sql table.
ppSqlTable :: [Attribute] -> SqlTable -> String
ppSqlTable as t = render (aBox // tBox)
  where 
    aBox = hsep 2 left (fmap (text . attributeName) as)
    tBox = vcat left (fmap (ppSqlRow as) t)

-- | boxes a sqlrow.
ppSqlRow :: [Attribute] -> SqlRow -> Box
ppSqlRow as r = hsep 2 left (fmap boxit as)
  where
   boxit a 
     | isNothing (M.lookup (attributeName a) r) 
       = emptyBox 1 1
     | otherwise 
       = text (show $ fromJust (M.lookup (attributeName a) r))


-- | looks up an attribute value in a tuple.
lookupAttValInSqlRow :: MonadThrow m => Attribute -> Relation -> SqlRow 
                                     -> m SqlValue
lookupAttValInSqlRow a r t 
  | M.member aName t = return $ fromJust (M.lookup aName t)
  | otherwise = throwM $ AttNotInRow a r t
    where
      aName = attributeName a

-- | returns a set of attributes from a tuple.
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
rowAttSet :: SqlRow -> Set Attribute
rowAttSet = S.map Attribute . M.keysSet 

-- | returns a set of attributes from a table.
tableAttSet :: SqlTable -> Set Attribute
tableAttSet [] = error "an empty table doesn't have any attributes"
tableAttSet t  = rowAttSet (head t)

-- | drops tuples that given config in the variant
--   their pres cond is unsat. the passed fexp is the
--   presence condition of the entire table.
dropUnsatTuples :: FeatureExpr -> PCatt -> SqlTable -> SqlTable
dropUnsatTuples f pc t = filter (satisfiable . tuple_pc) t
  where
    pcName = attributeName pc 
    tuple_pc tuple = And f ((sqlval2fexp . fromJust) $ M.lookup pcName tuple)

-- | forces a sqltable to conform to a table schema. i.e. 
--   it adds all attributes in the schema to the sqlvarianttable
--   with sqlnull.
-- it is totally ok if tuples have presence condition attribute.
conformSqlTableToSchema :: SqlTable -> RowType -> SqlTable
conformSqlTableToSchema t r =  map (flip conformSqlRowToRowType r) t

-- | construct the rowtype from a sqltable.
--   NOTE: it takes the first row of the table. so if that row
--         has a null value it may not be able to get the type 
--         correctly. for now make sure you never have a null
--         value in the first tuple. but fix it later!!
-- TODO: FIX THE ABOVE PROBLEM!!
-- DANGER: changed Attribute to (Attribute Nothing)
-- MAY CAUSE PROBLEMS!!!
constRowTypeOfSqlTable :: FeatureExpr -> SqlTable -> RowType
constRowTypeOfSqlTable f t = M.map (\v -> (f,v)) row''
  where 
    row   = head t 
    row'  = M.mapKeys (\s -> Attribute s) row 
    row'' = M.map typeOf row'

-- | inserts an attribute value pair to a sqlrow.
insertAttValToSqlRow :: Attribute -> SqlValue -> SqlRow -> SqlRow
insertAttValToSqlRow = M.insert . attributeName

-- | inserts an attribute value pair into all rows of a sqltable.
insertAttValToSqlTable :: Attribute -> SqlValue -> SqlTable -> SqlTable
insertAttValToSqlTable a v = map $ insertAttValToSqlRow a v 

-- | updates the pc of a tuple. 
--   assumption: the tuple has pc.
updatePCInSqlRow :: PCatt -> FeatureExpr -> SqlRow -> SqlRow
updatePCInSqlRow pc f = M.adjust (\_ -> fexp2sqlval f) (attributeName pc)

-- | updates the pc of a tuples in a table.
--   assumption: the tuple has pc.
updatePCInSqlTable :: PCatt -> FeatureExpr -> SqlTable -> SqlTable
updatePCInSqlTable pc f = map (updatePCInSqlRow pc f)

-- | forces a sqlrow to conform to a rowtype.
-- it is totally ok if the sqlrow have presence condition attribute.
conformSqlRowToRowType :: SqlRow -> RowType -> SqlRow
conformSqlRowToRowType r t = M.union r r'
  where
    rowTypeAtts = S.map attributeName $ getRowTypeAtts t 
    attDif      = rowTypeAtts S.\\ M.keysSet r 
    r'          = M.fromSet (\_ -> SqlNull) attDif

-- | combines a list of sqltables. it just appends tables for now.
-- TODO: s.t. it disjuncts the pc 
--   of the same tuple.
-- big assumption: the tables all have the same schema.
-- unionWithKey :: Ord k => (k -> a -> a -> a) -> Map k a -> Map k a -> Map k a
combineSqlTables :: PCatt -> [SqlTable] -> SqlTable
combineSqlTables _ = foldr (++) []
  -- where
  --   unionTwoTables lt rt = 


-----------apply conf------------------

-- | drops a row if it's pres cond is false.
dropRow :: PCatt -> SqlRow -> SqlRow
dropRow p r 
  | M.lookup (presCondAttName p) r == Just (fexp2sqlval $ Lit False)
  -- (toSql ("Lit False" :: String))
              = M.empty
  | otherwise = r

-- | drops rows that their pres cond is false.
dropRows :: PCatt -> SqlTable -> SqlTable
dropRows p t = filter (/= M.empty) $ fmap (dropRow p) t
  -- deleteBy (/=) M.empty $ fmap (dropRow p) t
-- dropRows c p = fmap $ M.filterWithKey filterRow
--   where filterRow att val = att == presCondAttName p 
--                             -- && val == SqlString "Lit False"
--                             && val == toSql ("Lit False" :: String)

-- filterWithKey :: (k -> a -> Bool) -> Map k a -> Map k a

-- | drops the pres cond key value in a row.
dropPres :: PCatt -> SqlRow -> SqlRow
dropPres p = M.delete (presCondAttName p)

-- | drops the pres cond key value in a table.
dropPresInTable :: PCatt -> SqlTable -> SqlTable
dropPresInTable p = fmap $ dropPres p

-- | applies a config to a table.
applyConfTable :: Config Bool -> PCatt -> FeatureExpr -> SqlTable -> SqlTable
applyConfTable c p f t = filter (evalFeatureExpr c . tuple_pc) t
  where
    tuple_pc tuple = And f ((sqlval2fexp . fromJust) $ M.lookup (attributeName p) tuple)


-- | applies a config to tables.
applyConfTables :: Config Bool -> PCatt -> FeatureExpr -> [SqlTable] -> [SqlTable]
applyConfTables c p f = fmap $ applyConfTable c p f 



