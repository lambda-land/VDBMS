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

eidValue :: C.Atom
eidValue = (C.Val (SqlInt32 123))

-- | All Feautres
encrypt, autoresponder, signature, remail,forwardmsg :: F.FeatureExpr
encrypt = F.Ref $ Feature "encrypt"
autoresponder = F.Ref $ Feature "autoresponder"
signature = F.Ref $ Feature "signature"
remail = F.Ref $ Feature "remail"
forwardmsg = F.Ref $ Feature "forwardmsg"


-- | Table reference 
v_employee, v_message, v_recipientinfo, v_auto_msg,v_forward_msg :: Algebra
v_employee = TRef (Relation "v_employee")
v_message = TRef (Relation "v_message")
v_recipientinfo = TRef (Relation "v_recipientinfo")
v_auto_msg = TRef (Relation "v_auto_msg")
v_forward_msg = TRef (Relation "v_forward_msg")
