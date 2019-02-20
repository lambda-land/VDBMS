 -- | Example Queries upon Enron Email Database
module VDB.Example.EnronUseCase.EnronQuery where

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

{-
--
-- ** Query in schema version 1 
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v1 :: Algebra
enronQ1_v1 =  Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee")


-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v1 :: Algebra
enronQ2_v1 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all employees who has remailmsg feature
-- SELECT eid, firstname, lastname
-- FROM v_employee, v_remail_msg
-- WHERE v_employee.mid = v_remail_msg.mid
enronQ3_v1 :: Algebra
enronQ3_v1 = let cond = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_employee"))  "mid")) (C.Attr (Attribute (Just "v_remail_msg") "mid"))
           in Proj (plainAttrs [ "eid","firstname", "lastname"]) $ Sel cond  $ SetOp Prod (TRef (Relation "v_employee")) (TRef (Relation "v_remail_msg"))


-- | a query that list all encrypted message body and subject 
-- SELECT mid, subject, body
-- FROM v_message
-- WHERE is_encrypted = True
enronQ4_v1 :: Algebra
enronQ4_v1 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "is_encrypted")) (C.Val (SqlBool True))
           in Proj (plainAttrs [ "mid", "subject", "body"]) $ Sel  cond  $ TRef (Relation "v_message")


--
-- ** Query in schema version 2
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v2 :: Algebra
enronQ1_v2 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))


-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v2 :: Algebra
enronQ2_v2 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all encrypted message body and subject 
-- SELECT mid, subject, body
-- FROM v_message
-- WHERE is_encrypted = True
enronQ4_v2 :: Algebra
enronQ4_v2 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "is_encrypted")) (C.Val (SqlBool True))
           in Proj (plainAttrs [ "mid", "subject", "body"]) $ Sel  cond  $ TRef (Relation "v_message")

--
-- ** Query in schema version 3 
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v3 :: Algebra
enronQ1_v3 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v3 :: Algebra
enronQ2_v3 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all employees who has remailmsg feature
-- SELECT eid, firstname, lastname
-- FROM v_employee, v_remail_msg
-- WHERE v_employee.mid = v_remail_msg.mid
enronQ3_v3 :: Algebra
enronQ3_v3 = let cond = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_employee"))  "mid")) (C.Attr (Attribute (Just "v_remail_msg") "mid"))
           in Proj (plainAttrs [ "eid","firstname", "lastname"]) $ Sel cond  $ SetOp Prod (TRef (Relation "v_employee")) (TRef (Relation "v_remail_msg"))

-- | a query that list all encrypted message body and subject 
-- SELECT mid, subject, body
-- FROM v_message
-- WHERE is_encrypted = True
enronQ4_v3 :: Algebra
enronQ4_v3 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "is_encrypted")) (C.Val (SqlBool True))
           in Proj (plainAttrs [ "mid", "subject", "body"]) $ Sel  cond  $ TRef (Relation "v_message")

--
-- ** Query in schema version 4
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v4 :: Algebra
enronQ1_v4 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v4 :: Algebra
enronQ2_v4 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all encrypted message body and subject 
-- SELECT mid, subject, body
-- FROM v_message
-- WHERE is_encrypted = True
enronQ4_v4 :: Algebra
enronQ4_v4 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "is_encrypted")) (C.Val (SqlBool True))
           in Proj (plainAttrs [ "mid", "subject", "body"]) $ Sel  cond  $ TRef (Relation "v_message")


--
-- ** Query in schema version 5
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v5 :: Algebra
enronQ1_v5 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v5 :: Algebra
enronQ2_v5 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all employees who has remailmsg feature
-- SELECT eid, firstname, lastname
-- FROM v_employee, v_remail_msg
-- WHERE v_employee.mid = v_remail_msg.mid
enronQ3_v5 :: Algebra
enronQ3_v5 = let cond = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_employee"))  "mid")) (C.Attr (Attribute (Just "v_remail_msg") "mid"))
           in Proj (plainAttrs [ "eid","firstname", "lastname"]) $ Sel cond  $ SetOp Prod (TRef (Relation "v_employee")) (TRef (Relation "v_remail_msg"))

--
-- ** Query in schema version 6
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v6 :: Algebra
enronQ1_v6 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v6 :: Algebra
enronQ2_v6 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

--
-- ** Query in schema version 7
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v7 :: Algebra
enronQ1_v7 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v7 :: Algebra
enronQ2_v7 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-- | a query that list all employees who has remailmsg feature
-- SELECT eid, firstname, lastname
-- FROM v_employee, v_remail_msg
-- WHERE v_employee.mid = v_remail_msg.mid
enronQ3_v7:: Algebra
enronQ3_v7 = let cond = C.Comp EQ (C.Attr (Attribute (Just (Relation "v_employee"))  "mid")) (C.Attr (Attribute (Just "v_remail_msg") "mid"))
           in Proj (plainAttrs [ "eid","firstname", "lastname"]) $ Sel cond  $ SetOp Prod (TRef (Relation "v_employee")) (TRef (Relation "v_remail_msg"))

--
-- ** Query in schema version 8 
--

 
-- | a query that list all employees with signature 
-- SELECT eid, firstname, lastname, signature
-- FROM v_employee
enronQ1_v8 :: Algebra
enronQ1_v8 =  (Proj (plainAttrs [ "eid", "firstname", "lastname", "signature"]) $ TRef (Relation "v_employee"))

-- | a query that list all manager's email and name 
-- SELECT firstname,lastname,email_id
-- FROM v_employee 
-- WHERE status = "Manager"
enronQ2_v8 :: Algebra
enronQ2_v8 = let cond = C.Comp EQ (C.Attr (Attribute Nothing "empno")) (C.Val (SqlString "Manager"))
           in Proj (plainAttrs [ "firstname", "lastname", "email_id"]) $ Sel  cond  $ TRef (Relation "v_employee")

-}

