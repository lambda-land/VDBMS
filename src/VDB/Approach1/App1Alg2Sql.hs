-- Approach1 translation of Variational relational algebra to SQL
-- with raw queries, queries are written in sql as text and passed 
-- to the rawQuery function
module VDB.Approach1.App1Alg2Sql where 

import Prelude hiding (Ordering(..))

import VDB.Algebra
import VDB.Name
import qualified VDB.FeatureExpr as F
import qualified VDB.Condition as C 
import VDB.Variational
import VDB.Type
import VDB.SAT
import VDB.Schema

import Data.Convertible (safeConvert)
import Data.Bifunctor (second)
import Data.List (groupBy)
import qualified Data.Text as T (Text, pack, append, concat, intercalate)
import Data.Maybe (catMaybes)

type Vquery = Opt T.Text
type Vsubquery = Opt T.Text

transVerify :: Algebra -> F.FeatureExpr -> [Vquery]
transVerify q ctxt = catMaybes $ map verifyVquery vqs
  where 
    vqs = trans q ctxt

-- | verifies a vquery to ensure that the fexp is satisfiable.
--   and shrinks the presence condition assigned to the query.
verifyVquery :: Vquery -> Maybe Vquery
verifyVquery vq 
  | satisfiable fexp = Just $ mkOpt (F.shrinkFeatureExpr fexp) (getObj vq)
  | otherwise = Nothing
  where
    fexp = getFexp vq 


-- | translates a vq to a list of vqs runnable in a relational db engine.
--   little optimization is combined with it, e.g., 
--   sel sel == sel.
--   sel prj == prj sel instead of prj *
trans :: Algebra -> F.FeatureExpr -> [Vquery]
trans (SetOp Prod l r) ctxt = case (l, r) of 
  (TRef l', TRef r') -> [mkOpt ctxt $ T.concat ["select * from ", T.pack $ relationName l',
    "  join ", T.pack $ relationName r']]
  -- (TRef _, Empty) -> trans l ctxt -- these two are captured by the more general
  -- (Empty, TRef _) -> trans r ctxt -- rule (Empty,_)
  (Empty, _) -> trans r ctxt -- note: this captures (Empty,Empty) too!
  (_, Empty) -> trans l ctxt
  (TRef l', _) -> [mkOpt rf $ T.concat ["select * from ", T.pack $ relationName l',
    " join ( ", rt, " ) "] | (rf,rt) <- rres]
      where 
        rres = trans r ctxt
  (_, TRef r') -> [mkOpt lf $ T.concat ["select * from ( ", lt, " ) join ", 
    T.pack $ relationName r'] | (lf,lt) <- lres]
      where
        lres = trans l ctxt
  _ -> [mkOpt (F.And lf rf) $ T.concat ["select * from ( ", lt, " ) join ( ", rt, " ) "]
    | (lf,lt) <- lres, (rf,rt) <- rres]
      where
        lres = trans l ctxt
        rres = trans r ctxt
trans (SetOp o l r) ctxt = case (l,r) of
  (TRef l', TRef r') -> [mkOpt ctxt $ T.concat ["select * from ", T.pack $ relationName l', ot,
    " select * from ", T.pack $ relationName r']]
  (Empty, Empty) -> trans Empty ctxt
  (TRef l', _) -> [mkOpt rf $ T.concat ["select * from ", T.pack $ relationName l', ot, rt] 
    | (rf,rt) <- rres]
      where
        rres = trans r ctxt
  (_, TRef r') -> [mkOpt lf $ T.concat [lt, ot, " select * from ", T.pack $ relationName r']
    | (lf,lt) <- lres]
      where 
        lres = trans l ctxt
  _ -> [mkOpt (F.And lf rf) $ T.concat [lt, ot, rt] | (lf,lt) <- lres, (rf,rt) <- rres]
    where 
      lres = trans l ctxt
      rres = trans r ctxt
  where 
    ot = if o == Union then " union " else " except"
trans (Proj oas q)  ctxt = case oas of 
  [] -> error "syntactically incorrect vq! cannot have an empty list of vatt!!"
  _  -> case q of 
    Proj oas' q' -> trans (Proj (oas ++ oas') q') ctxt
    -- [mkOpt (F.And (F.And af qf) af') $ T.concat ["select ", at, " , ", at', " from ( ", qt, " ) "]
    --   | (af,at) <- ares, (af',at') <- ares', (qf,qt) <- qres]
    --     where 
    --       ares = prjAux oas 
    --       ares' = prjAux oas'
    --       qres = trans q' ctxt    
    Sel c q' -> [mkOpt (F.And (F.And af cf) qf) $ T.concat ["select ", at, " from ( ", qt, " ) where ", ct]
      | (af,at) <- ares, (cf,ct) <- cres, (qf,qt) <- qres]
        where
          cres = selAux c ctxt
          qres = trans q' ctxt
    SetOp Prod l r -> case (l,r) of
      (TRef l', TRef r') -> [mkOpt (F.And ctxt af) $ T.concat ["select ", at, " from ", T.pack $ relationName l',
        " join ", T.pack $ relationName r'] | (af,at) <- ares]
      (Empty, _) -> trans r ctxt
      (_, Empty) -> trans l ctxt
      (TRef l', _) -> [mkOpt (F.And af rf) $ T.concat ["select ", at, " from ", T.pack $ relationName l',
        " join ( ", rt, " ) "] | (af,at) <- ares, (rf,rt) <- rres]
          where
            rres = trans r ctxt
      (_, TRef r') -> [mkOpt (F.And af lf) $ T.concat ["select ", at, " from ( ", lt, " ) join ",
        T.pack $ relationName r'] | (af,at) <- ares, (lf,lt) <- lres]
          where
            lres = trans l ctxt
      _ -> [mkOpt (F.And (F.And lf rf) af) $ T.concat ["select ", at, " from ( ", lt, " ) join ( ", rt, " ) "]
        | (af,at) <- ares, (lf,lt) <- lres, (rf,rt) <- rres]
          where
            rres = trans r ctxt
            lres = trans l ctxt
    SetOp o l r -> case (l,r) of
      (TRef l', TRef r') -> [mkOpt (F.And af ctxt) $ T.concat ["select ", at, " from ", T.pack $ relationName l',
        ot, " select ", at, " from ", T.pack $ relationName r'] | (af,at) <- ares]
      (Empty, Empty) -> trans Empty ctxt
      (TRef l', _) -> [mkOpt (F.And af rf) $ T.concat ["select ", at, " from ", T.pack $ relationName l',
        ot, " select ", at, " from ( ", rt, " ) "] | (af,at) <- ares, (rf,rt) <- rres]
          where
            rres = trans r ctxt
      (_, TRef r') -> [mkOpt (F.And af lf) $ T.concat ["select ", at, " from ( ", lt, " ) ", ot, 
        " select ", at, " from ", T.pack $ relationName r'] | (af,at) <- ares, (lf,lt) <- lres]
          where 
            lres = trans l ctxt
      _ -> [mkOpt (F.And (F.And lf rf) af) $ T.concat ["select ", at, " from ( ", lt, " ) ", ot,
        " select ", at, " from ( ", rt, " ) "] | (af,at) <- ares, (lf,lt) <- lres, (rf,rt) <- rres]
          where
            lres = trans l ctxt
            rres = trans r ctxt
      where
        -- ares = prjAux oas
        ot = if o == Union then " union " else " except"
    TRef r -> [mkOpt (F.And af ctxt) $ T.concat ["select ", at, " from ", T.pack $ relationName r] 
      | (af,at) <- ares]
        where 
          ares  = prjAux oas 
    Empty -> error "syntactically incorrect vq! cannot project attributes from empty!"
    _ -> [mkOpt (F.And af qf) $ T.concat ["select ", at, " from ( ", qt, " ) "]
      | (af,at) <- ares, (qf,qt) <- qres]
        where 
          qres = trans q ctxt 
          -- ares = prjAux oas 
    where
      ares = prjAux oas 
trans (Sel c q)     ctxt = case q of 
  SetOp Prod l r -> case (l,r) of 
    (TRef l', TRef r') -> [mkOpt cf $ T.concat ["select * from ", T.pack $ relationName l',
      " join ", T.pack $ relationName r', " where ", ct] | (cf,ct) <- cres]
    (Empty, _) -> trans (Sel c r) ctxt
    (_, Empty) -> trans (Sel c l) ctxt
    (_, TRef r') -> [mkOpt (F.And cf lf) $ T.concat ["select * from ( ", lt, " ) join ", 
      T.pack $ relationName r', " where ", ct] | (cf,ct) <- cres, (lf,lt) <- lres]
        where
          lres = trans l ctxt
    (TRef l', _) -> [mkOpt (F.And cf rf) $ T.concat ["select * from ", T.pack $ relationName l',
      " join ( ", rt, " ) where ", ct] | (cf,ct) <- cres, (rf,rt) <- rres]
        where
          rres = trans r ctxt
    _ -> [mkOpt (F.And (F.And lf rf) cf) $ T.concat ["select * from ( ", lt, " ) join ( ", 
      rt, " ) where ", ct] | (cf,ct) <- cres, (rf,rt) <- rres, (lf,lt) <- lres]
        where
          rres = trans r ctxt
          lres = trans l ctxt
    where 
      cres = selAux c ctxt
  SetOp o l r -> case (l,r) of
    (TRef l', TRef r') -> [mkOpt cf $ T.concat ["select * from ", T.pack $ relationName l', 
      " where ", ct, ot, " select * from ", T.pack $ relationName r', " where ", ct]
      | (cf,ct) <- cres]
    (Empty, Empty) -> trans Empty ctxt
    (TRef l', _) -> [mkOpt (F.And cf rf) $ T.concat ["select * from ", T.pack $ relationName l',
      " where ", ct, ot, " select * from ( ", rt, " ) where ", ct] | (cf,ct) <- cres, (rf,rt) <- rres]
        where
          rres = trans r ctxt
    (_, TRef r') -> [mkOpt (F.And cf lf) $ T.concat ["select * from ( ", lt, " ) where ", ct, ot,
      " select * from ", T.pack $ relationName r', " where ", ct] | (cf,ct) <- cres, (lf,lt) <- lres]
        where 
          lres = trans l ctxt
    _ -> [mkOpt (F.And (F.And lf rf) cf) $ T.concat ["select * from ( ", lt, " ) where ", ct, ot,
      " select * from ( ", rt, " ) where ", ct] | (cf,ct) <- cres, (lf,lt) <- lres, (rf,rt) <- rres]
        where 
          rres = trans r ctxt
          lres = trans l ctxt
    where 
      cres = selAux c ctxt
      ot = if o == Union then " union " else " except"
  Proj as q' -> trans (Proj as $ Sel c q') ctxt
  -- [mkOpt (F.And (F.And qf cf) af) $ T.concat ["select ", at, " from ( ", qt, " ) where ", ct]
  --   | (af,at) <- ares, (cf,ct) <- cres, (qf,qt) <- qres]
  --     where 
  --       ares = prjAux as 
  --       qres = trans q' ctxt
  --       cres = selAux c ctxt
  Sel c' q' -> trans (Sel (C.And c c') q') ctxt
  -- [mkOpt (F.And cf' (F.And cf qf)) $ T.concat ["select * from ( ", qt, " ) where ", ct, " and ", ct']
  --   | (cf',ct') <- cres', (cf,ct) <- cres, (qf,qt) <- qres]
  --     where 
  --       cres = selAux c ctxt
  --       cres' = selAux c' ctxt
  --       qres = trans q' ctxt
  TRef r -> [mkOpt cf $ T.concat ["select * from ", T.pack $ relationName r, " where ", ct]
    | (cf,ct) <- cres]
      where 
        cres = selAux c ctxt
  Empty -> error "syntactically incorrect vq!! cannot select anything from empty!!"
  _ -> [mkOpt (F.And cf qf) (T.concat ["select * from ( ", qt, " ) where ", ct])
    | (cf,ct) <- cres, (qf,qt) <- qres]
      where 
        cres = selAux c ctxt 
        qres = trans q ctxt 
trans (AChc f l r)  ctxt = case (l, r) of 
  (Empty, Empty) -> trans Empty ctxt 
  (Empty, rq)    -> trans rq (F.And (F.Not f) ctxt)
  (lq, Empty)    -> trans lq (F.And f ctxt)
  (lq, rq)       -> lres ++ rres
    where 
      lres = trans lq (F.And f ctxt)
      rres = trans rq (F.And (F.Not f) ctxt)
trans (TRef r)      ctxt = [mkOpt ctxt $ T.append "select * from " $ T.pack (relationName r)]
trans (Empty)       ctxt = [mkOpt ctxt  "select null"]  


-- | helper function for the projection query with qualified attributes.
prjAux :: [Opt Attribute] -> [Vsubquery]
prjAux oa = map (second (T.intercalate ", ")) groupedAttsText
  -- map (second (T.concat . map getAttName)) groupedAtts'
  where 
    groupedAtts     = groupBy (\x y -> fst x == fst y) oa
    groupedAtts'    = map pushDownList' groupedAtts -- [(fexp,[attribute])]

--     groupedAttsText = map (second $ map (T.pack . attributeName)) groupedAtts'

    groupedAttsText = map (second $ map (T.pack . getAttName)) groupedAtts'


-- | helper function for projection without qualified attributes.
-- prjAuxUnqualified :: [Opt Attribute] -> [Vsubquery]
-- prjAuxUnqualified oa = map (second (T.intercalate ", ")) groupedAttsText
--   where 
--     groupedAtts     = groupBy (\x y -> fst x == fst y) oa
--     groupedAtts'    = map pushDownList' groupedAtts -- [(fexp,[attribute])]
--     groupedAttsText = map (second $ map getAttNameUnqualified) groupedAtts'

-- | constructs a list of attributes that have the same fexp.
--   NOTE: this is unsafe since you're not checking if 
--         the second element of pairs are the same!
pushDownList' :: [(a,b)] -> (a,[b])
pushDownList' [(a,b)] = (a,[b])
pushDownList' ((a,b):l) = (a,b:snd (pushDownList' l))

-- <<<<<<< enronUsecase

-- | returns an attribute name with its qualified relation name if available.
-- NOTE: it doesn't return qualified attributes!
-- getAttName :: Attribute -> T.Text
-- getAttName (Attribute a)   = T.append (T.pack a) " "
-- getAttName (Attribute a)   = T.append (T.pack a) " "
-- getAttName (Attribute (Just r) a)  = T.concat [T.pack $ relationName r, ".", T.pack a, " "]

-- | get unquilified attribute names.
-- getAttNameUnqualified :: Attribute -> T.Text
-- getAttNameUnqualified (Attribute a)   = T.append (T.pack a) " "


-- | helper function for selection.
selAux :: C.Condition -> F.FeatureExpr -> [Vsubquery]
selAux (C.Lit b)      ctx = [mkOpt ctx $ T.pack $ show b]
selAux (C.Comp op latom ratom) ctx = [mkOpt ctx $ 
  T.concat[T.pack $ show latom, T.pack $ show op, T.pack $ show ratom]]
selAux (C.Not c)      ctx = map (second (\q -> T.concat ["not ( ", q, " ) "])) cres
  where cres = selAux c ctx
selAux (C.Or l r)     ctx = [mkOpt (F.And fl fr) (T.concat [" ( ", ql, " ) or ( ", qr, " ) "]) 
  | (fl,ql) <- lres, (fr,qr) <- rres]
  where 
    lres = selAux l ctx
    rres = selAux r ctx
selAux (C.And l r)    ctx = [mkOpt (F.And fl fr) (T.concat [" ( ", ql, " ) and ( ", qr, " ) "]) 
  | (fl,ql) <- lres, (fr,qr) <- rres]
  where 
    lres = selAux l ctx
    rres = selAux r ctx
selAux (C.CChc f l r) ctx = lres ++ rres
  where
    lres = selAux l (F.And f ctx)
    rres = selAux r (F.And (F.Not f) ctx)

-- | tests:
-- v1, v2, v3, v4, v5 :: F.FeatureExpr
-- v1 = F.Ref "v_1"
-- v2 = F.Ref "v_2"
-- v3 = F.Ref "v_3"
-- v4 = F.Ref "v_4"
-- v5 = F.Ref "v_5"

-- fexp1, fexp2 :: F.FeatureExpr
-- fexp1 = F.Lit True
-- fexp2 = F.Or (F.Or v3 v4) v5

-- q1, q2, q3, q4, q5, q6 :: Algebra 
-- -- q1 = Proj [(F.Lit True, Attribute (Just $ Relation "v_dept") "deptname")] $ TRef $ Relation "v_dept"
-- -- select v_dept.deptname  from v_dept
-- q1 = Proj [(F.Lit True, Attribute (Just $ Relation "v_dept") "deptname"), 
--            (F.Lit True, Attribute (Just $ Relation "v_dept") "deptno")] $ TRef $ Relation "v_dept" 
-- -- select v_dept.deptname , v_dept.deptno  from v_dept
-- -- q2 = Sel (C.Lit True) $ TRef $ Relation "v_dept" 
-- -- select * from v_dept where True
-- q2 = Sel (C.Lit True) q1
-- q3 = undefined
-- q4 = undefined
-- q5 = undefined
-- q6 = undefined


-- vqManual = AChc (Ref $ Feature "v1") empQ1_v1 
--                  (AChc (Or (Ref $ Feature "v2") (Ref $ Feature "v3")) empQ1_v2 
--                   empQ1_v4and5)



