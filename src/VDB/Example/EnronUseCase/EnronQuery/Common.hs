module VDB.Example.EnronUseCase.EnronQuery.Common where 

import VDB.Algebra
import qualified VDB.Condition as C
import qualified VDB.FeatureExpr as F
import VDB.Name
import VDB.Variational 
import Database.HDBC
import VDB.Type
import Prelude hiding (Ordering(..))
import Data.Time

import VDB.Example.SmartConstructor

-- | the message id value we choose for entire use case
midValue :: C.Atom
midValue = (C.Val (SqlInt32 9138))

midValueFromRemailer :: C.Atom
midValueFromRemailer = (C.Val (SqlInt32 1082))

midValueEncrypted :: C.Atom 
midValueEncrypted = (C.Val (SqlInt32 2893))

eidValue :: C.Atom
eidValue = (C.Val (SqlInt32 123))

nullValue :: C.Atom 
nullValue = C.Val SqlNull

trueValue :: C.Atom
trueValue = C.Val (SqlBool True)

falseValue :: C.Atom
falseValue = C.Val (SqlBool False)
-- | All Feautres
encrypt, autoresponder, signature, remailmsg,forwardmsg :: F.FeatureExpr
encrypt = F.Ref $ Feature "encrypt"
autoresponder = F.Ref $ Feature "autoresponder"
signature = F.Ref $ Feature "signature"
remailmsg = F.Ref $ Feature "remailmsg"
forwardmsg = F.Ref $ Feature "forwardmsg"


-- | Table reference 
v_employee, v_message, v_recipientinfo, v_auto_msg,v_forward_msg :: Algebra
v_employee = TRef (Relation "v_employee")
v_message = TRef (Relation "v_message")
v_recipientinfo = TRef (Relation "v_recipientinfo")
v_auto_msg = TRef (Relation "v_auto_msg")
v_forward_msg = TRef (Relation "v_forward_msg")
v_remail_msg = TRef (Relation "v_remail_msg")



-- 
-- * Join tables
-- 
-- | Join v_employee + v_message 
joinMsgEmp :: Algebra
joinMsgEmp = SetOp Prod v_message v_employee 

joinMsgEmpCond :: C.Condition
joinMsgEmpCond = C.Comp EQ (C.Attr (genQAtt ("v_message","sender"))) (C.Attr (genQAtt ("v_employee","email_id")))


-- | join v_employee + v_message + v_recipientinfo
joinMsgEmpRec :: Algebra
joinMsgEmpRec = SetOp Prod v_message $ SetOp Prod v_employee  v_recipientinfo 

joinMsgEmpRecCond :: C.Condition
joinMsgEmpRecCond = C.And cond1 cond2
    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_message","mid"))) (C.Attr (genQAtt ("v_recipientinfo","mid")))
          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_recipientinfo","rvalue"))) (C.Attr (genQAtt ("v_employee","email_id")))

-- | Join v_forward with v_employee + v_message + v_recipientinfo
joinForwardEmpRecMsg :: Algebra
joinForwardEmpRecMsg = SetOp Prod v_forward_msg joinMsgEmpRec

joinForwardRecMsgEmpCond :: C.Condition
joinForwardRecMsgEmpCond  = C.And cond joinMsgEmpRecCond 
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_forward_msg","eid"))) (C.Attr (genQAtt ("v_employee","eid")))
                          

-- | Join v_remail with v_employee + v_message + v_recipientinfo
joinRemailEmpRecMsg :: Algebra
joinRemailEmpRecMsg = SetOp Prod v_remail_msg joinMsgEmpRec

joinRemailEmpRecMsgCond :: C.Condition
joinRemailEmpRecMsgCond  = C.And cond joinMsgEmpRecCond
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_remail_msg","eid"))) (C.Attr (genQAtt ("v_employee","eid")))

-- | Join v_auto_msg with v_employee + v_message + v_recipientinfo
joinAutoEmpRecMsgCond :: C.Condition
joinAutoEmpRecMsgCond  = C.And cond joinMsgEmpRecCond
                    where cond = C.Comp EQ (C.Attr (genQAtt ("v_auto_msg","eid"))) (C.Attr (genQAtt ("v_employee","eid")))

joinAutoEmpRecMsg :: Algebra
joinAutoEmpRecMsg = SetOp Prod v_auto_msg joinMsgEmpRec

-- | Join v_employee with  v_forward_msg + v_remail_msg
joinEmpForwardRemailCond :: C.Condition 
joinEmpForwardRemailCond = C.And cond1 cond2
    where cond1 = C.Comp EQ (C.Attr (genQAtt ("v_employee","eid"))) (C.Attr (genQAtt ("v_forward_msg","eid")))
          cond2 = C.Comp EQ (C.Attr (genQAtt ("v_employee","eid"))) (C.Attr (genQAtt ("v_remail_msg","eid")))

joinEmpForwardRemail :: Algebra
joinEmpForwardRemail = SetOp Prod v_employee (SetOp Prod v_forward_msg v_remail_msg)
