CREATE TABLE v_employee (
  eid integer NOT NULL DEFAULT '0',
  firstName varchar(31) NOT NULL DEFAULT '',
  lastName varchar(31) NOT NULL DEFAULT '',
  email_id varchar(31) NOT NULL DEFAULT '',
  folder varchar(31) NOT NULL DEFAULT '',
  status varchar(50)  DEFAULT NULL,
  sign text,
  public_key varchar(31) DEFAULT NULL,
  presCond text
);

CREATE TABLE v_message (
  mid integer NOT NULL DEFAULT '0',
  sender varchar(127)  NOT NULL DEFAULT '',
  date timestamp DEFAULT NULL,
  message_id varchar(127)  DEFAULT NULL,
  subject text,
  body text ,
  folder varchar(127) NOT NULL DEFAULT '',
  is_system_notification boolean DEFAULT NULL,
  is_signed boolean DEFAULT NULL,
  is_encrypted boolean DEFAULT NULL,
  is_from_remailer boolean DEFAULT NULL,
  is_autoresponse boolean DEFAULT NULL,
  is_forward_msg boolean DEFAULT NULL,
  presCond text
);

create type emailtype as enum ('TO', 'CC', 'BCC');

CREATE TABLE v_recipientinfo (
  rid integer NOT NULL DEFAULT '0',
  mid integer  NOT NULL DEFAULT '0',
  rtype emailtype DEFAULT NULL,
  rvalue varchar(127) DEFAULT NULL,
  dater timestamp DEFAULT NULL,
  presCond text
);

CREATE TABLE v_referenceinfo (
  rfid integer NOT NULL DEFAULT '0',
  mid integer NOT NULL DEFAULT '0',
  reference text,
  presCond text
);

CREATE TABLE v_auto_msg (
  eid integer NOT NULL,
  subject varchar(41) DEFAULT NULL,
  body varchar(244) DEFAULT NULL,
  presCond text
);

CREATE TABLE v_forward_msg (
  eid integer NOT NULL DEFAULT '0',
  forwardAddr varchar(31)  DEFAULT NULL,
  presCond text
);

CREATE TABLE v_remail_msg (
  eid integer NOT NULL DEFAULT '0',
  pseudonym varchar(8) DEFAULT NULL,
  presCond text
);

CREATE TABLE v_filter_msg (
  eid integer NOT NULL DEFAULT '0',
  suffix varchar(31) DEFAULT NULL,
  presCond text
);

CREATE TABLE v_mailhost (
  eid integer NOT NULL DEFAULT '0',	
  username varchar(31) DEFAULT NULL,
  mailhost varchar(31) DEFAULT NULL,
  presCond text
);

CREATE TABLE v_alias (
  eid integer NOT NULL DEFAULT '0',
  email_id varchar(127)   DEFAULT NULL,
  nickname varchar(127)  DEFAULT NULL,
  presCond text
);