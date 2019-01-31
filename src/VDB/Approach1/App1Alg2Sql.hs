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

import Data.Convertible (safeConvert)
import Data.Bifunctor (second)
import Data.List (groupBy)
import qualified Data.Text as T (Text, pack, append, concat)
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


-- TODO: add opt after trans where you send fexp to sat! to also drop the invalid qs
trans :: Algebra -> F.FeatureExpr -> [Vquery]
trans (SetOp s l r) ctxt = [setAux s lq rq | lq <- lres, rq <- rres]
  where 
    lres = trans l ctxt
    rres = trans r ctxt
trans (Proj oas q)  ctxt = [mkOpt (F.And af qf) $ T.concat ["select ", at, qt]
  | (af,at) <- ares, (qf,qt) <- qres]
  where 
    qres = trans q ctxt
    ares  = prjAux oas 
trans (Sel c q)     ctxt = [mkOpt (F.And cf qf) (T.concat [qt, " where ", ct])
  | (cf,ct) <- cres, (qf,qt) <- qres]
  where 
    cres = selAux c ctxt
    qres = trans q ctxt
trans (AChc f l r)  ctxt = lres ++ rres
  where 
    lres = trans l (F.And f ctxt)
    rres = trans r (F.And (F.Not f) ctxt)
trans (TRef r)      ctxt = [mkOpt ctxt $ T.pack (relationName r)]
trans (Empty)       ctxt = [mkOpt ctxt  "select null"]

-- | helper function for Setop queries, i.e., union, diff, prod
-- TODO: check!!!
setAux :: SetOp -> Vquery -> Vquery -> Vquery
setAux Union = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat [l, " union ", r])
setAux Diff  = \(lo, l) (ro, r) -> ((F.And lo (F.Not ro)), T.concat [l, " minus ", r])
setAux Prod  = \(lo, l) (ro, r) -> ((F.And lo ro), T.concat [ l, " join ", r])
-- setAux Prod  = \(lo, l) (ro, r) -> ((F.Or lo ro), T.concat ["select * from (" , l, ") join (", r, ")"]) -- the OLD one!!

-- | helper function for the projection query
prjAux :: [Opt Attribute] -> [Vsubquery]
prjAux oa = map (second (T.concat . map getAttName)) groupedAtts'
  where 
    groupedAtts = groupBy (\x y -> fst x == fst y) oa
    groupedAtts' = map pushDownList' groupedAtts -- [(fexp,[attribute])]


-- | constructs a list of attributes that have the same fexp.
--   NOTE: this is unsafe since you're not checking if 
--         the second element of pairs are the same!
pushDownList' :: [(a,b)] -> (a,[b])
pushDownList' [(a,b)] = (a,[b])
pushDownList' ((a,b):l) = (a,b:snd (pushDownList' l))


-- | returns an attribute name with its qualified relation name if available.
getAttName :: Attribute -> T.Text
getAttName (Attribute Nothing a)   = T.append (T.pack a) " "
getAttName (Attribute (Just r) a)  = T.concat [T.pack $ relationName r, ".", T.pack a, " "]

-- | helper function for selection.
selAux :: C.Condition -> F.FeatureExpr -> [Vsubquery]
selAux (C.Lit b)      ctx = [mkOpt ctx $ T.pack $ show b]
selAux (C.Comp op latom ratom) ctx = [mkOpt ctx $ 
  T.concat[showAtom latom, showComp op, showAtom ratom]]
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

-- | helper for selAux.
showComp :: CompOp -> T.Text
showComp EQ  = " == "
showComp NEQ = " <> "
showComp LT  = " < "
showComp LTE = " <= "
showComp GTE = " >= "
showComp GT  = " > "

-- | helper for selAux.
showAtom :: C.Atom -> T.Text
showAtom (C.Val v)  = case safeConvert v of 
  Right val -> T.pack val
  _ -> error "safeConvert resulted in error!!! showAtom"
showAtom (C.Attr a) = getAttName a
  -- case attributeQualifier a of 
  -- Just r  -> T.concat[T.pack $ relationName r, ".", T.pack $ attributeName a]
  -- Nothing -> T.pack $ attributeName a 

-- | tests:



