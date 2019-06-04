module VDB.Example.EnronUseCase.EnronQuery.SignatureRemail where 

import VDB.Example.EnronUseCase.EnronQuery.Common
import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import VDB.Type
import Prelude hiding (Ordering(..))


-- * NOTE: implement before is_remail column introduced

-- 
-- 5. interaction between sign with remail
-- 
-- * Situdation: Bob sign a message that is then sent though the remail(use pseudonyms), 
--   the recipient receive the signed message, defeating the anonymity.
-- * Fix with VDB: use presence condition to force those two feature do not interact.
-- * V-Query: signature AND (NOT remail) <Q1, Empty>


enronVQ5 :: Algebra
enronVQ5 = AChc (F.And signature (F.Not remailmsg)) u5_Q1 Empty

u5_Q1 :: Algebra
u5_Q1 = Proj (map trueAtt $ genQAtts [("v_employee", "email_id"), ("v_employee", "sign")]) 
        $ Sel cond 
        $ v_employee
        where cond = C.Comp EQ (C.Attr (genQAtt ("v_employee","eid"))) eidValue


-- | translated Query 

-- select email_id, sign, concat("signature", " AND ", "(NOT remailmsg)") as presCond
-- from v_employee 
-- where eid = 123

