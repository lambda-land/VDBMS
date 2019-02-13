 -- | An example schema 
module VDB.Example.EnronUseCase.EnronSchema where

import VDB.Schema
import VDB.FeatureExpr
import VDB.Name
import VDB.Type
import VDB.Variational
import VDB.Config

import qualified Data.Map as M 
import VDB.Example.SmartConstructor


-- 
--  Features
-- 

signature,addressbook, filtermsg, encrypt, autoresponder, forwardmsg, mailhost, remailmsg :: Feature
signature     = Feature "signature"
addressbook   = Feature "addressbook"
filtermsg     = Feature "filtermsg"
encrypt       = Feature "encryption"
autoresponder = Feature "autoresponder"
forwardmsg    = Feature "forwardmsg"
mailhost      = Feature "mailhost"
remailmsg     = Feature "remailmsg"

-- 
-- Feature expressions
-- 

-- | FeatureExpr for  (signature, addressbook, filtermsg)
sign_addr_filter :: FeatureExpr
sign_addr_filter = (Ref signature) `And` (Ref addressbook) `And` (Ref filtermsg)

-- | FeatureExpr for encrption
encryption :: FeatureExpr 
encryption = Ref encrypt

-- | FeatureExpr for (autoresponder, forwardmsg, mailhost)
auto_forward_mhost :: FeatureExpr
auto_forward_mhost = (Ref autoresponder) `And` (Ref forwardmsg) `And` (Ref mailhost)

remail :: FeatureExpr
remail = Ref remailmsg

-- 
-- Relation names
-- 
v_employee, v_message, v_recipientInfo, v_referenceInfo, v_auto_msg, v_forward_msg,
  v_remail_msg, v_filter_msg, v_mailhost, v_alias :: String
v_employee      = "v_employee"
v_message       = "v_message"
v_recipientInfo = "v_recipientInfo"
v_referenceInfo = "v_referenceInfo"
v_auto_msg      = "v_auto_msg"
v_forward_msg   = "v_forward_msg"
v_remail_msg    = "v_remail_msg"
v_filter_msg    = "v_filter_msg"
v_mailhost      = "v_mailhost"
v_alias         = "v_alias"

-- 
-- Attribute names
-- 

--
-- ** schema 1
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                    (autoresponder, forwardmsg, mailhost),
--                     remailmsg
--    * disable feature: None

-- | A configuration of enron email that disables all features.
enronConfigAllDisabled :: Config Bool
enronConfigAllDisabled = disableAll

-- | enron email first configuration.
enronConfig1 :: Config Bool
enronConfig1 = enableMany 
  [signature, addressbook, filtermsg, encrypt, autoresponder, forwardmsg, 
   mailhost, remailmsg] enronConfigAllDisabled

enronSchema1 :: Schema 
enronSchema1 = ( sign_addr_filter `And` encryption `And` auto_forward_mhost `And` remail, 
								   constructRelMap [ ( v_employee,  employeelist_v1)
                                                   , ( v_message,    message_v1)
                                                   , ( v_recipientInfo,  recipientInfo_v1)
                                                   , ( v_referenceInfo,  referenceInfo_v1)
                                                   , ( v_auto_msg,  recipientInfo_v1)
                                                   , ( v_forward_msg,  recipientInfo_v1)
                                                   , ( v_remail_msg,  recipientInfo_v1)
                                                   , ( v_filter_msg,  recipientInfo_v1)
                                                   , ( v_mailhost,  mailhost_v1)
                                                   , ( v_alias,  alias_v1)

                                                   ]
               )

-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v1 :: [(String, SqlType)]
employeelist_v1 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("puclic_key", TString)
	           , ("did", TInt32)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v1 :: [(String, SqlType)]
message_v1 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           , ("is_encrypted", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v1 :: [(String, SqlType)]
recipientInfo_v1 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v1 :: [(String, SqlType)]
referenceInfo_v1 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v1 :: [(String, SqlType)]
auto_msg_v1 =  [ ("eid", TInt32) 
	           ,  ("subject",  TString)
	           , ("body",  TString)
	           ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v1 :: [(String, SqlType)]
forward_msg_v1 =  [ ("eid", TInt32)
	              , ("forwardaddr",  TString)
	              ]

-- remail_msg(eid, psuedonym, presCond)
remail_msg_v1 :: [(String, SqlType)]
remail_msg_v1 =   [ ("eid", TInt32) 
	              , ("psuedonym",  TString)
	              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v1 :: [(String, SqlType)]
filter_msg_v1 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]

-- mailhost(did, domain, presCond)
mailhost_v1 :: [(String, SqlType)]
mailhost_v1 = [ ("did", TInt32)
	          , ("domain",  TString)
	          ]

-- alias(eid, email, nickname, presCond)
alias_v1 :: [(String, SqlType)]
alias_v1 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]

--
-- ** schema 2
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                    (autoresponder, forwardmsg, mailhost),
--                     
--    * disable feature: remailmsg

enronSchema2 :: Schema 
enronSchema2 = ( sign_addr_filter `Or` encryption `Or` auto_forward_mhost, 
								   constructRelMap [ ( "employeelist_v2",  employeelist_v2)
                                                   , ( "message_v2",    message_v2)
                                                   , ( "recipientInfo_v2",  recipientInfo_v2)
                                                   , ( "referenceInfo_v2",  referenceInfo_v2)
                                                   , ( "auto_msg_v2",  recipientInfo_v2)
                                                   , ( "forward_msg_v2",  recipientInfo_v2)
                                                   , ( "filter_msg_v2",  recipientInfo_v2)
                                                   , ( "mailhost_v1",  mailhost_v1)
                                                   , ( "alias_v2",  alias_v2)

                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key,did, presCond)
employeelist_v2 :: [(String, SqlType)]
employeelist_v2 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("did", TInt32)
	           , ("puclic_key", TString)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v2 :: [(String, SqlType)]
message_v2 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           , ("is_encrypted", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v2 :: [(String, SqlType)]
recipientInfo_v2 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v2 :: [(String, SqlType)]
referenceInfo_v2 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v2 :: [(String, SqlType)]
auto_msg_v2 =  [ ("eid", TInt32) 
	           ,  ("subject",  TString)
	           , ("body",  TString)
	           ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v2 :: [(String, SqlType)]
forward_msg_v2 =  [ ("eid", TInt32)
	              , ("forwardaddr",  TString)
	              ]


-- filter_msg(eid, suffix, presCond)
filter_msg_v2 :: [(String, SqlType)]
filter_msg_v2 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]

-- mailhost(did, domain, presCond)
mailhost_v2 :: [(String, SqlType)]
mailhost_v2 = [ ("did", TInt32)
	          , ("domain",  TString)
	          ]

-- alias(eid, email, nickname, presCond)
alias_v2 :: [(String, SqlType)]
alias_v2 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]


--
-- ** schema 3
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                     remailmsg
--    * disable feature: (autoresponder, forwardmsg, mailhost)


enronSchema3 :: Schema 
enronSchema3 = ( sign_addr_filter `Or` encryption `Or` remail, 
								   constructRelMap [ ( "employeelist_v3",  employeelist_v3)
                                                   , ( "message_v3",    message_v3)
                                                   , ( "recipientInfo_v3",  recipientInfo_v3)
                                                   , ( "referenceInfo_v3",  referenceInfo_v3)
                                                   , ( "remail_msg_v3",  recipientInfo_v3)
                                                   , ( "filter_msg_v3",  recipientInfo_v3)
                                                   , ( "alias_v3",  alias_v3)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v3 :: [(String, SqlType)]
employeelist_v3 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("puclic_key", TString)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v3 :: [(String, SqlType)]
message_v3 =  [ ("mid", TInt32) 
	           , ("sender",  TString)
	           , ("date",  TString)
	           , ("message_id", TInt32)
	           , ("subject", TString)
	           , ("body", TString)
	           , ("folder", TString)
	           , ("is_signed", TBool)
	           , ("is_encrypted", TBool)
	           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v3 :: [(String, SqlType)]
recipientInfo_v3 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v3 :: [(String, SqlType)]
referenceInfo_v3 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- remail_msg(eid, psuedonym, presCond)
remail_msg_v3 :: [(String, SqlType)]
remail_msg_v3 =   [ ("eid", TInt32) 
	              , ("psuedonym",  TString)
	              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v3 :: [(String, SqlType)]
filter_msg_v3 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]


-- alias(eid, email, nickname, presCond)
alias_v3 :: [(String, SqlType)]
alias_v3 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]


--
-- ** schema 4
--    * enable feature: (signature, addressbook, filtermsg), 
--                     encryption, 
--                     
--    * disable feature: (autoresponder, forwardmsg, mailhost)
--                       remailmsg


enronSchema4 :: Schema 
enronSchema4 = ( sign_addr_filter `Or` encryption, 
								   constructRelMap [ ( "employeelist_v4",  employeelist_v4)
                                                   , ( "message_v4",    message_v4)
                                                   , ( "recipientInfo_v4",  recipientInfo_v4)
                                                   , ( "referenceInfo_v4",  referenceInfo_v4)
                                                   , ( "filter_msg_v4",  recipientInfo_v4)
                                                   , ( "alias_v4",  alias_v4)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, puclic_key, did, presCond)
employeelist_v4 :: [(String, SqlType)]
employeelist_v4 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("puclic_key", TString)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, is_encrypted, presCond)
message_v4 :: [(String, SqlType)]
message_v4 =  [ ("mid", TInt32) 
	           , ("sender",  TString)
	           , ("date",  TString)
	           , ("message_id", TInt32)
	           , ("subject", TString)
	           , ("body", TString)
	           , ("folder", TString)
	           , ("is_signed", TBool)
	           , ("is_encrypted", TBool)
	           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v4 :: [(String, SqlType)]
recipientInfo_v4 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v4 :: [(String, SqlType)]
referenceInfo_v4 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- filter_msg(eid, suffix, presCond)
filter_msg_v4 :: [(String, SqlType)]
filter_msg_v4 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]


-- alias(eid, email, nickname, presCond)
alias_v4 :: [(String, SqlType)]
alias_v4 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]


--
-- ** schema 5
--    * enable feature: (signature, addressbook, filtermsg), 
--                    (autoresponder, forwardmsg, mailhost),
--                     remailmsg
--    * disable feature: encryption
--                     


enronSchema5 :: Schema 
enronSchema5 = ( sign_addr_filter `Or` auto_forward_mhost `Or` remail, 
	                               constructRelMap [ ( "employeelist_v5",  employeelist_v5)
                                                   , ( "message_v5",    message_v5)
                                                   , ( "recipientInfo_v5",  recipientInfo_v5)
                                                   , ( "referenceInfo_v5",  referenceInfo_v5)
                                                   , ( "auto_msg_v5",  recipientInfo_v5)
                                                   , ( "forward_msg_v5",  recipientInfo_v5)
                                                   , ( "remail_msg_v5",  recipientInfo_v5)
                                                   , ( "filter_msg_v5",  recipientInfo_v5)
                                                   , ( "mailhost_v5",  mailhost_v5)
                                                   , ( "alias_v5",  alias_v5)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, did, presCond)
employeelist_v5 :: [(String, SqlType)]
employeelist_v5 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("did", TInt32)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v5 :: [(String, SqlType)]
message_v5 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v5 :: [(String, SqlType)]
recipientInfo_v5 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]

-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v5 :: [(String, SqlType)]
referenceInfo_v5 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v5 :: [(String, SqlType)]
auto_msg_v5 =  [ ("eid", TInt32) 
	           ,  ("subject",  TString)
	           , ("body",  TString)
	           ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v5 :: [(String, SqlType)]
forward_msg_v5 =  [ ("eid", TInt32)
	              , ("forwardaddr",  TString)
	              ]

-- remail_msg(eid, psuedonym, presCond)
remail_msg_v5 :: [(String, SqlType)]
remail_msg_v5 =   [ ("eid", TInt32) 
	              , ("psuedonym",  TString)
	              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v5 :: [(String, SqlType)]
filter_msg_v5 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]

-- mailhost(did, domain, presCond)
mailhost_v5 :: [(String, SqlType)]
mailhost_v5 = [ ("did", TInt32)
	          , ("domain",  TString)
	          ]

-- alias(eid, email, nickname, presCond)
alias_v5 :: [(String, SqlType)]
alias_v5 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]

--
-- ** schema 6
--    * enable feature: (signature, addressbook, filtermsg), 
--                    (autoresponder, forwardmsg, mailhost),
--                     
--    * disable feature: encryption
--                      ,remailmsg
--                     


enronSchema6 :: Schema 
enronSchema6 = ( sign_addr_filter `Or` auto_forward_mhost, 
								   constructRelMap [ ( "employeelist_v6",  employeelist_v6)
                                                   , ( "message_v6",    message_v6)
                                                   , ( "recipientInfo_v6",  recipientInfo_v6)
                                                   , ( "referenceInfo_v6",  referenceInfo_v6)
                                                   , ( "auto_msg_v6",  recipientInfo_v6)
                                                   , ( "forward_msg_v6",  recipientInfo_v6)
                                                   , ( "filter_msg_v6",  recipientInfo_v6)
                                                   , ( "mailhost_v6",  mailhost_v6)
                                                   , ( "alias_v6",  alias_v6)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign, did, presCond)
employeelist_v6 :: [(String, SqlType)]
employeelist_v6 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           , ("did", TInt32)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v6 :: [(String, SqlType)]
message_v6 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v6 :: [(String, SqlType)]
recipientInfo_v6 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]

-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v6 :: [(String, SqlType)]
referenceInfo_v6 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]


-- auto_msg(eid, subject, body,presCond)
auto_msg_v6 :: [(String, SqlType)]
auto_msg_v6 =  [ ("eid", TInt32) 
	           ,  ("subject",  TString)
	           , ("body",  TString)
	           ]

-- forward_msg(eid,forwardaddr, presCond)
forward_msg_v6 :: [(String, SqlType)]
forward_msg_v6 =  [ ("eid", TInt32)
	              , ("forwardaddr",  TString)
	              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v6 :: [(String, SqlType)]
filter_msg_v6 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]

-- mailhost(did, domain, presCond)
mailhost_v6 :: [(String, SqlType)]
mailhost_v6 = [ ("did", TInt32)
	          , ("domain",  TString)
	          ]

-- alias(eid, email, nickname, presCond)
alias_v6 :: [(String, SqlType)]
alias_v6 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]

--
-- ** schema 7
--    * enable feature: (signature, addressbook, filtermsg), 
--                      remailmsg
--    * disable feature: encryption, 
--                       (autoresponder, forwardmsg, mailhost),



enronSchema7 :: Schema 
enronSchema7 = (sign_addr_filter `Or` remail, 
	                               constructRelMap [ ( "employeelist_v7",  employeelist_v7)
                                                   , ( "message_v7",    message_v7)
                                                   , ( "recipientInfo_v7",  recipientInfo_v7)
                                                   , ( "referenceInfo_v7",  referenceInfo_v7)
                                                   , ( "remail_msg_v7",  recipientInfo_v7)
                                                   , ( "filter_msg_v7",  recipientInfo_v7)
                                                   , ( "alias_v7",  alias_v7)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign,  presCond)
employeelist_v7 :: [(String, SqlType)]
employeelist_v7 = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v7 :: [(String, SqlType)]
message_v7 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v7 :: [(String, SqlType)]
recipientInfo_v7 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v7 :: [(String, SqlType)]
referenceInfo_v7 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]



-- remail_msg(eid, psuedonym, presCond)
remail_msg_v7 :: [(String, SqlType)]
remail_msg_v7 =   [ ("eid", TInt32) 
	              , ("psuedonym",  TString)
	              ]

-- filter_msg(eid, suffix, presCond)
filter_msg_v7 :: [(String, SqlType)]
filter_msg_v7 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]


-- alias(eid, email, nickname, presCond)
alias_v7 :: [(String, SqlType)]
alias_v7 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]

--
-- ** schema 8
--    * enable feature: (signature, addressbook, filtermsg), 
--
--    * disable feature: encryption, 
--                       (autoresponder, forwardmsg, mailhost),
--                       remailmsg



enronSchema8 :: Schema 
enronSchema8 = ( sign_addr_filter, constructRelMap [ ( "employeelist_v8",  employeelist_v8)
                                                   , ( "message_v8",    message_v8)
                                                   , ( "recipientInfo_v8",  recipientInfo_v8)
                                                   , ( "referenceInfo_v8",  referenceInfo_v8)
                                                   , ( "filter_msg_v8",  recipientInfo_v8)
                                                   , ( "alias_v8",  alias_v8)
                                                   ]
               )


-- employeelist(eid, firstname, lastname, email_id, folder, status, sign,  presCond)
employeelist_v8 :: [(String, SqlType)]
employeelist_v8  = [ ("eid", TInt32), 
	             ("firstname",  TString)
	           , ("lastname",  TString)
	           , ("email_id", TString)
	           , ("folder", TString)
	           , ("status", TString)
	           , ("sign", TString)
	           ]


-- message(mid, sender, date, message_id, subject, body, folder, is_signed, presCond)
message_v8 :: [(String, SqlType)]
message_v8 =  [ ("mid", TInt32) 
		           , ("sender",  TString)
		           , ("date",  TString)
		           , ("message_id", TInt32)
		           , ("subject", TString)
		           , ("body", TString)
		           , ("folder", TString)
		           , ("is_signed", TBool)
		           ]

-- recipientInfo(rid, mid, rtype. rvalue_email, rvalue_nickname, presCond)
recipientInfo_v8 :: [(String, SqlType)]
recipientInfo_v8 = [ ("rid", TInt32)
		           , ("mid",  TInt32)
		           , ("rtype",  TString)
		           , ("rvalue_email", TString)
		           , ("rvalue_nickname", TString)
		           ]
-- referenceInfo(rfid, mid,reference, presCond)
referenceInfo_v8 :: [(String, SqlType)]
referenceInfo_v8 = [ ("rfid", TInt32)
		           , ("mid",  TInt32)
		           , ("reference",  TString)
		           ]



-- filter_msg(eid, suffix, presCond)
filter_msg_v8 :: [(String, SqlType)]
filter_msg_v8 = [ ("eid", TInt32) 
	            , ("suffix",  TString)
	            ]


-- alias(eid, email, nickname, presCond)
alias_v8 :: [(String, SqlType)]
alias_v8 = [ ("eid", TInt32)
	       , ("email",  TString)
	       , ("nickname",  TString)
	       ]

