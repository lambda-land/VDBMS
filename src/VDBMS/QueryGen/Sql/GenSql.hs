-- | generates sql queries from sql queries/ra queries
--   and renames subqueries/relations without an alias.
module VDBMS.QueryGen.Sql.GenSql (

         genSql
       , nameSubSql

) where 

-- import VDBMS.QueryLang.RelAlg.Relational.Algebra 
import VDBMS.QueryLang.SQL.Pure.Sql
import VDBMS.QueryLang.SQL.Condition (SqlCond(..),RCondition(..))
import VDBMS.QueryLang.RelAlg.Relational.Algebra
-- import VDBMS.QueryTrans.AlgebraToSql (transAlgebra2Sql)
import VDBMS.VDB.Name 
-- import VDBMS.QueryLang.SQL.Condition 
-- import VDBMS.QueryLang.RelAlg.Basics.SetOp
-- import VDBMS.VDB.Schema.Variational.Schema

-- import Data.List ((\\))

import Control.Monad.State 

import Data.Maybe (isNothing, fromJust)

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as SM

import Debug.Trace

-- | number for generating names.
type AliasNum = Int 

type RenameEnv = SM.Map Relation Name 

data StateInfo = StateInfo 
  { counter :: AliasNum
  , env :: RenameEnv
  }

incCounter :: StateInfo -> StateInfo
incCounter (StateInfo c e) = StateInfo (c+1) e

addR2env :: Relation -> StateInfo -> StateInfo
addR2env r (StateInfo c e) = StateInfo (c+1) (SM.insert r ("t" ++ show c) e)

-- -- | A Query monad provides unique names (aliases)
-- --   and constructs a SqlSelect.
-- type QState = State AliasNum SqlSelect
type QState = State StateInfo 
-- data Query  = Query (QState -> QState)

-- | evaluates the qstate with zero.
evalQState :: QState a -> a
evalQState = flip evalState initState
  where initState = StateInfo 0 SM.empty

-- | gives names to a subqueries and relations of a given
--   sql query.
genSql :: Sql -> Sql
-- genSql = trace "checking00000000000" $ 
genSql = evalQState . nameSubSql 

-- TODO: attributes qualifiers must also be updated.
-- | names subqueries within a sql query.
nameSubSql :: Sql -> QState Sql
nameSubSql (Sql (SelectFromWhere as ts cs))
  -- = trace "checking111111111111" $ 
  = do ts' <- mapM nameRel ts
       renv <- gets env
       let as' = updateAttsQual as ts' renv 
           cs' = updateCondsQual cs ts' renv
       return $ Sql (SelectFromWhere as' ts' cs')
  -- = mapM nameRels ts >>= return (\ts' -> SqlSelect as ts' cs)
nameSubSql (SqlBin o lq rq) 
  = do lq' <- nameSubSql lq
       rq' <- nameSubSql rq 
       return $ SqlBin o lq' rq'
nameSubSql q = return q

-- | names a sql relation without a name.
-- nameRel :: [SqlAttrExpr] -> [SqlCond SqlSelect] -> Rename SqlRelation 
--         -> QState (Rename SqlRelation)
nameRel :: Rename SqlRelation -> QState (Rename SqlRelation)
nameRel rq@(Rename a q@(SqlSubQuery subq)) 
  | isNothing a && isrel subq
    = do subq' <- nameSubSql subq
         s <- gets counter
         let rq' = Rename (Just ("t" ++ show s)) (SqlSubQuery subq')
         if isrel subq 
         then modify (addR2env (sqlrel subq))
         else modify id 
         return rq'
  | isNothing a && issqlslct subq 
    -- = trace "checking!!!!!!!!" $ 
    = do subq' <- nameSubSql subq
         s <- gets counter
         let rq' = Rename (Just ("t" ++ show s)) (SqlSubQuery subq')
         if null (sqlattributes subq) 
         then return $ Rename Nothing (SqlSubQuery subq')
         else do modify incCounter
                 return rq'
  | otherwise = return rq
-- TODO: we may need to updates condition for attributes qualifiers.
nameRel rq@(Rename a (SqlInnerJoin l r c)) 
  | isNothing a 
    = trace (show c) $ 
      do l' <- nameRel l
         r' <- nameRel r
         -- s <- gets counter
         renv <- gets env
         let c' = updateJCondQual c l' r' renv
             rq' = Rename Nothing (SqlInnerJoin l' r' c')
         -- modify 
         return $ rq'
  | otherwise = error "an inner join shouldn't have a name"
    -- where
    --   la = name l 
    --   ra = name r

-- |
updateAttsQual :: [SqlAttrExpr] -> [Rename SqlRelation] -> RenameEnv 
               -> [SqlAttrExpr]
updateAttsQual as rs e = map (flip (flip updateAttQual rs) e) as 

-- -- |
updateAttQual :: SqlAttrExpr -> [Rename SqlRelation] -> RenameEnv 
              -> SqlAttrExpr
updateAttQual ae@(SqlAttr (Rename Nothing at@(Attr _ q))) _ e 
  | isNothing q = ae
  | isQualRel aq 
    = SqlAttr (Rename Nothing (updateAttrQual at (SubqueryQualifier aq')))
      where 
        aq = fromJust q
        aq' = fromJust (SM.lookup (relQualifier aq) e)
updateAttQual _ _ _ = error "updateAttQual. GenSql. shoulnt have got such SqlAttrExpr"

-- |
updateJCondQual :: RCondition 
                -> Rename SqlRelation -> Rename SqlRelation
                -> RenameEnv
                -> RCondition
updateJCondQual c ls rs e = updateRCondQual c [ls,rs] e 

-- |
updateCondsQual :: [SqlCond Sql] -> [Rename SqlRelation] -> RenameEnv
               -> [SqlCond Sql]
updateCondsQual cs rs e = map (flip (flip updateCondQual rs) e) cs

-- |
updateRCondQual :: RCondition -> [Rename SqlRelation] -> RenameEnv
                -> RCondition
updateRCondQual c@(RLit _) _ _ = c
updateRCondQual (RComp o l r) rs e = RComp o l' r' 
  where
    l' = updateAtomQual l rs e
    r' = updateAtomQual r rs e 
updateRCondQual (RNot c) rs e = RNot c'
  where
    c' = updateRCondQual c rs e
updateRCondQual (ROr l r) rs e = ROr l' r'
  where 
    l' = updateRCondQual l rs e
    r' = updateRCondQual r rs e
updateRCondQual (RAnd l r) rs e = RAnd l' r'
  where 
    l' = updateRCondQual l rs e
    r' = updateRCondQual r rs e

updateAtomQual :: Atom -> [Rename SqlRelation] -> RenameEnv -> Atom
updateAtomQual at@(Att a) _ e
  | isNothing aq = at 
  | isQualRel (fromJust aq) = Att $
    updateAttrQual 
      a 
      (SubqueryQualifier 
        (fromJust (SM.lookup (relQualifier (fromJust aq)) e)))
  | otherwise = at 
    where
      aq = qualifier a 
updateAtomQual v _ _ = v

-- |
updateCondQual :: SqlCond Sql -> [Rename SqlRelation] -> RenameEnv
               -> SqlCond Sql
updateCondQual (SqlCond c)  rs e = SqlCond $ updateRCondQual c rs e
updateCondQual c@(SqlIn _ _) _ _ = c
updateCondQual (SqlNot c)   rs e = SqlNot $ updateCondQual c rs e 
updateCondQual (SqlOr l r)  rs e = SqlOr l' r'
  where
    l' = updateCondQual l rs e
    r' = updateCondQual r rs e
updateCondQual (SqlAnd l r) rs e = SqlAnd l' r' 
  where
    l' = updateCondQual l rs e
    r' = updateCondQual r rs e




