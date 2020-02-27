--
-- Table structure for table `v_employee`
-- v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, prescond)
--

DROP TABLE IF EXISTS `v_employee`;
SET character_set_client = utf8mb4 ;
CREATE TABLE `v_employee` (
  `eid` int(10) unsigned NOT NULL,
  `firstName` varchar(31) NOT NULL,
  `lastName` varchar(31) NOT NULL,
  `email_id` varchar(31) NOT NULL,
  `folder` varchar(31) NOT NULL,
  `status` varchar(50)  DEFAULT NULL,
  `verification_key` text DEFAULT NULL,
  `public_key` varchar(31) DEFAULT NULL,
  `prescond` text
);

-- enhanced email
INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, verification_key, public_key, prescond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL, 
"forwardmsg and filtermsg and (not (addressbook or encrypt or remailmsg or autoresponder or signature or mailhost))"
FROM p1_employee_view;

-- privacy-focus email
INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, verification_key, public_key, prescond)
SELECT eid, firstname, lastname, email_id, folder, status, verification_key, public_key, 
"signature and encrypt and remailmsg and (not (addressbook or filtermsg or autoresponder or forwardmsg or mailhost))"
FROM p2_employee_view;

-- group email
INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, verification_key, public_key, prescond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL,
"addressbook and autoresponder and mailhost and encrypt and signature and (not (forwardmsg or remailmsg or filtermsg))"
FROM p3_employee_view ;

-- premium email
INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, verification_key, public_key, prescond)
SELECT eid, firstname, lastname, email_id, folder, status, verification_key, public_key,
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg"
FROM p4_employee_view ;

-- basic email
INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, verification_key, public_key, prescond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL,
"(not signature) and (not addressbook) and (not filtermsg) and (not autoresponder) and (not forwardmsg) and (not mailhost) and (not encrypt) and (not remailmsg)"
FROM p5_employee_view ;


--
-- Table structure for table `v_message`
-- v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
--

DROP TABLE IF EXISTS `v_message`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_message` (
  `mid` int(10) NOT NULL,
  `sender` varchar(127)  NOT NULL,
  `date` datetime DEFAULT NULL,
  `message_id` varchar(127)  DEFAULT NULL,
  `subject` text,
  `body` text ,
  `folder` varchar(127) NOT NULL,
  `is_system_notification` boolean DEFAULT NULL,
  `is_signed` boolean DEFAULT NULL,
  `is_encrypted` boolean DEFAULT NULL,
  `is_autoresponse` boolean DEFAULT NULL,
  `is_forward_msg` boolean DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;
INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, NULL, NULL, NULL, is_forward_msg, 
"forwardmsg and filtermsg and (not (addressbook or encrypt or remailmsg or autoresponder or signature or mailhost))"
FROM p1_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, NULL, NULL,
"signature and encrypt and remailmsg and (not (addressbook or filtermsg or autoresponder or forwardmsg or mailhost))"
FROM p2_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, NULL, 
"addressbook and autoresponder and mailhost and encrypt and signature and (not (forwardmsg or remailmsg or filtermsg))"
FROM p3_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg,
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg"
FROM p4_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_autoresponse, is_forward_msg, prescond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, NULL, NULL, NULL, NULL, 
"(not signature) and (not addressbook) and (not filtermsg) and (not autoresponder) and (not forwardmsg) and (not mailhost) and (not encrypt) and (not remailmsg)"
FROM p5_message_view;

--
-- Table structure for table `v_recipientinfo`
-- v_recipientinfo(rid, mid, rtype, rvalue, prescond) 
--

DROP TABLE IF EXISTS `v_recipientinfo`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_recipientinfo` (
  `rid` int(10) NOT NULL,
  `mid` int(10) unsigned NOT NULL,
  `rtype` enum('TO','CC','BCC') DEFAULT NULL,
  `rvalue` varchar(127) DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_recipientinfo(rid, mid, rtype, rvalue, prescond)
 (SELECT rec.*
 FROM p1_recipientinfo_view rec)
 union
 (SELECT rec.*
 FROM p2_recipientinfo_view rec)
 union
 (SELECT rec.*
 FROM p3_recipientinfo_view rec)
 union
 (SELECT rec.*
 FROM p4_recipientinfo_view rec)
 union
 (SELECT rec.*
 FROM p5_recipientinfo_view rec);

--
-- Table structure for table `v_auto_msg`
--

DROP TABLE IF EXISTS `v_auto_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_auto_msg` (
  `eid` int(11) NOT NULL,
  `subject` varchar(41) DEFAULT NULL,
  `body` varchar(244) DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_auto_msg(eid, subject, body, prescond)
SELECT eid, subject, body, 
"addressbook and mailhost and encrypt and signature"
FROM p3_auto_msg_view;

INSERT INTO v_auto_msg(eid, subject, body, prescond)
SELECT eid, subject, body, 
"signature and addressbook and filtermsg and forwardmsg and mailhost and encrypt and remailmsg"
FROM p4_auto_msg_view;

--
-- Table structure for table `v_forward_msg`
-- v_forward_msg(eid, forwardaddr, prescond)
--

DROP TABLE IF EXISTS `v_forward_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_forward_msg` (
  `eid` int(10) unsigned NOT NULL,
  `forwardAddr` varchar(31)  DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_forward_msg(eid, forwardaddr, prescond)
SELECT eid, forwardaddr, 
"filtermsg"
FROM p1_forward_msg_view;

INSERT INTO v_forward_msg(eid, forwardaddr, prescond)
SELECT eid, forwardaddr, 
"signature and addressbook and filtermsg and autoresponder and mailhost and encrypt and remailmsg"
FROM p4_forward_msg_view;

--
-- Table structure for table `v_remail_msg`
-- v_remail_msg(eid, pseudonym, prescond)

--

DROP TABLE IF EXISTS `v_remail_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_remail_msg` (
  `eid` int(10) unsigned NOT NULL,
  `pseudonym` varchar(8) DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_remail_msg(eid, pseudonym, prescond)
SELECT  eid, pseudonym, 
"signature and encrypt"
FROM p2_remail_msg_view;

INSERT INTO v_remail_msg(eid, pseudonym, prescond)
SELECT  eid, pseudonym, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and mailhost and encrypt"
FROM p4_remail_msg_view;

--
-- Table structure for table `v_filter_msg`
--

DROP TABLE IF EXISTS `v_filter_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_filter_msg` (
  `eid` int(10) unsigned NOT NULL,
  `suffix` varchar(31) DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_filter_msg(eid, suffix, prescond)
SELECT eid, suffix, 
"forwardmsg"
FROM p1_filter_msg_view;

INSERT INTO v_filter_msg(eid, suffix, prescond)
SELECT eid, suffix, 
"signature and addressbook and autoresponder and forwardmsg and mailhost and encrypt and remailmsg"
FROM p4_filter_msg_view;

--
-- Table structure for table `v_mailhost`
-- v_mailhost(eid, username, mailhost, prescond)
--

DROP TABLE IF EXISTS `v_mailhost`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_mailhost` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',  
  `username` varchar(31) DEFAULT NULL,
  `mailhost` varchar(31) DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB AUTO_INCREMENT=51 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_mailhost(eid, username, mailhost, prescond)
SELECT eid, username, mailhost, 
"addressbook and autoresponder and encrypt and signature"
FROM p3_mailhost_view;

INSERT INTO v_mailhost(eid, username, mailhost, prescond)
SELECT eid, username, mailhost, 
"signature and addressbook and filtermsg and autoresponder and forwardmsg and encrypt and remailmsg"
FROM p4_mailhost_view;

--
-- Table structure for table `v_alias`
--

DROP TABLE IF EXISTS `v_alias`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_alias` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',
  `email_id` varchar(127)   DEFAULT NULL,
  `nickname` varchar(127)  DEFAULT NULL,
  `prescond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_alias(eid, email_id, nickname, prescond)
SELECT eid, email_id, nickname, 
"autoresponder and mailhost and encrypt and signature"
FROM p3_alias_view;

INSERT INTO v_alias(eid, email_id, nickname, prescond)
SELECT eid, email_id, nickname, 
"signature and filtermsg and autoresponder and forwardmsg and mailhost and encrypt and remailmsg"
FROM p4_alias_view;

