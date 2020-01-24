--
-- Table structure for table `v_employee`
-- v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
--

DROP TABLE IF EXISTS `v_employee`;
SET character_set_client = utf8mb4 ;
CREATE TABLE `v_employee` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',
  `firstName` varchar(31) NOT NULL DEFAULT '',
  `lastName` varchar(31) NOT NULL DEFAULT '',
  `email_id` varchar(31) NOT NULL DEFAULT '',
  `folder` varchar(31) NOT NULL DEFAULT '',
  `status` varchar(50)  DEFAULT NULL,
  `sign` text,
  `public_key` varchar(31) DEFAULT NULL,
  `presCond` text
);
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL, 
"forwardmsg AND filtermsg AND NOT (addressbook OR encrypt OR remailmsg OR autoresponder OR signature OR mailhost)"
FROM p1_employee_view;

INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
SELECT eid, firstname, lastname, email_id, folder, status, sign, public_key, 
"signature AND encrypt AND remailmsg AND NOT (addressbook OR filtermsg OR autoresponder OR forwardmsg OR mailhost)"
FROM p2_employee_view;

INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL,
"addressbook AND autoresponder AND mailhost AND NOT (forwardmsg OR encrypt OR remailmsg OR filtermsg OR signature)"
FROM p3_employee_view ;

INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
SELECT eid, firstname, lastname, email_id, folder, status, sign, public_key,
"signature AND addressbook AND filtermsg AND autoresponder AND forwardmsg AND mailhost AND encrypt AND remailmsg"
FROM p4_employee_view ;

INSERT INTO v_employee(eid, firstname, lastname, email_id, folder, status, sign, public_key, presCond)
SELECT eid, firstname, lastname, email_id, folder, status, NULL, NULL,
"(NOT signature) AND (NOT addressbook) AND (NOT filtermsg) AND (NOT autoresponder) AND (NOT forwardmsg) AND (NOT mailhost) AND (NOT encrypt) AND (NOT remailmsg)"
FROM p5_employee_view ;


--
-- Table structure for table `v_message`
-- v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
--

DROP TABLE IF EXISTS `v_message`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_message` (
  `mid` int(10) NOT NULL DEFAULT '0',
  `sender` varchar(127)  NOT NULL DEFAULT '',
  `date` datetime DEFAULT NULL,
  `message_id` varchar(127)  DEFAULT NULL,
  `subject` text,
  `body` text ,
  `folder` varchar(127) NOT NULL DEFAULT '',
  `is_system_notification` int(1) DEFAULT NULL,
  `is_signed` int(1) DEFAULT NULL,
  `is_encrypted` int(1) DEFAULT NULL,
  `is_from_remailer` int(1) DEFAULT NULL,
  `is_autoresponse` int(1) DEFAULT NULL,
  `is_forward_msg` int(1) DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;
INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, NULL, NULL, NULL, NULL, is_forward_msg, 
"forwardmsg AND filtermsg AND NOT (addressbook OR encrypt OR remailmsg OR autoresponder OR signature OR mailhost)"
FROM p1_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, NULL, NULL,
"signature AND encrypt AND remailmsg AND NOT (addressbook OR filtermsg OR autoresponder OR forwardmsg OR mailhost)"
FROM p2_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, NULL, NULL, NULL, is_autoresponse, NULL, 
"addressbook AND autoresponder AND mailhost AND NOT (forwardmsg OR encrypt OR remailmsg OR filtermsg OR signature)"
FROM p3_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg,
"signature AND addressbook AND filtermsg AND autoresponder AND forwardmsg AND mailhost AND encrypt AND remailmsg"
FROM p4_message_view;

INSERT INTO v_message(mid, sender, date, message_id, subject, body, folder, is_system_notification, is_signed, is_encrypted, is_from_remailer, is_autoresponse, is_forward_msg, presCond) 
SELECT mid, sender, date, message_id, subject, body, folder, is_system_notification, NULL, NULL, NULL, NULL, NULL, 
"(NOT signature) AND (NOT addressbook) AND (NOT filtermsg) AND (NOT autoresponder) AND (NOT forwardmsg) AND (NOT mailhost) AND (NOT encrypt) AND (NOT remailmsg)"
FROM p5_message_view;

--
-- Table structure for table `v_recipientinfo`
-- v_recipientinfo(rid, mid, rtype, rvalue, presCond) 
--

DROP TABLE IF EXISTS `v_recipientinfo`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_recipientinfo` (
  `rid` int(10) NOT NULL DEFAULT '0',
  `mid` int(10) unsigned NOT NULL DEFAULT '0',
  `rtype` enum('TO','CC','BCC') DEFAULT NULL,
  `rvalue` varchar(127) DEFAULT NULL,
  `dater` datetime DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `v_referenceinfo`
-- v_auto_msg(eid, subject, body, presCond)
--

DROP TABLE IF EXISTS `v_referenceinfo`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_referenceinfo` (
  `rfid` int(10) NOT NULL DEFAULT '0',
  `mid` int(10) NOT NULL DEFAULT '0',
  `reference` text,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

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
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_auto_msg(eid, subject, body, presCond)
SELECT eid, subject, body, 
"TRUE"
FROM auto_msg_view;

--
-- Table structure for table `v_forward_msg`
-- v_forward_msg(eid, forwardaddr, presCond)
--

DROP TABLE IF EXISTS `v_forward_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_forward_msg` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',
  `forwardAddr` varchar(31)  DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_forward_msg(eid, forwardaddr, presCond)
SELECT eid, forwardaddr,
"TRUE"
FROM forward_msg_view;

--
-- Table structure for table `v_remail_msg`
-- v_remail_msg(eid, pseudonym, presCond)

--

DROP TABLE IF EXISTS `v_remail_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_remail_msg` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',
  `pseudonym` varchar(8) DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_remail_msg(eid, pseudonym, presCond)
SELECT  eid, pseudonym, "TRUE"
FROM remail_msg_view;

--
-- Table structure for table `v_filter_msg`
--

DROP TABLE IF EXISTS `v_filter_msg`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_filter_msg` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',
  `suffix` varchar(31) DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_filter_msg(eid, suffix, presCond)
SELECT eid, suffix, "TRUE"
FROM filter_msg_view;


--
-- Table structure for table `v_mailhost`
-- v_mailhost(eid, username, mailhost, presCond)
--

DROP TABLE IF EXISTS `v_mailhost`;
/*!40101 SET @saved_cs_client     = @@character_set_client */;
 SET character_set_client = utf8mb4 ;
CREATE TABLE `v_mailhost` (
  `eid` int(10) unsigned NOT NULL DEFAULT '0',	
  `username` varchar(31) DEFAULT NULL,
  `mailhost` varchar(31) DEFAULT NULL,
  `presCond` text
) ENGINE=InnoDB AUTO_INCREMENT=51 DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_mailhost(eid, username, mailhost, presCond)
SELECT eid, username, mailhost, "TRUE"
FROM mailhost_view;

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
  `presCond` text
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb4 COLLATE=utf8mb4_0900_ai_ci;
/*!40101 SET character_set_client = @saved_cs_client */;

INSERT INTO v_alias(eid, email_id, nickname, presCond)
SELECT eid, email_id, nickname, "TRUE"
FROM alias_view;
