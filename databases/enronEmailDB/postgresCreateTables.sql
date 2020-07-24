CREATE TABLE v_employee (
  eid integer NOT NULL,
  firstName varchar(31) NOT NULL,
  lastName varchar(31) NOT NULL,
  email_id varchar(31) NOT NULL,
  folder varchar(31) NOT NULL,
  status varchar(50) DEFAULT NULL,
  verification_key text DEFAULT NULL,
  public_key varchar(31) DEFAULT NULL,
  prescond text
);

CREATE TABLE v_message (
  mid integer NOT NULL,
  sender varchar(127)  NOT NULL,
  date timestamp DEFAULT NULL,
  message_id varchar(127)  DEFAULT NULL,
  subject text,
  body text ,
  folder varchar(127) NOT NULL DEFAULT '',
  is_system_notification smallint DEFAULT NULL,
  is_signed smallint DEFAULT NULL,
  is_encrypted smallint DEFAULT NULL,
  is_autoresponse smallint DEFAULT NULL,
  is_forward_msg smallint DEFAULT NULL,
  prescond text
);

create type emailtype as enum ('TO', 'CC', 'BCC');

CREATE TABLE v_recipientinfo (
  rid integer NOT NULL,
  mid integer  NOT NULL,
  rtype emailtype DEFAULT NULL,
  rvalue varchar(127) DEFAULT NULL,
  prescond text
);

CREATE TABLE v_auto_msg (
  eid integer NOT NULL,
  subject text DEFAULT NULL,
  body text DEFAULT NULL,
  prescond text
);

CREATE TABLE v_forward_msg (
  eid integer NOT NULL,
  forwardAddr varchar(31)  DEFAULT NULL,
  prescond text
);

CREATE TABLE v_remail_msg (
  eid integer NOT NULL,
  pseudonym varchar(8) DEFAULT NULL,
  prescond text
);

CREATE TABLE v_filter_msg (
  eid integer NOT NULL,
  suffix varchar(31) DEFAULT NULL,
  prescond text
);

CREATE TABLE v_mailhost (
  eid integer NOT NULL,	
  username varchar(31) DEFAULT NULL,
  mailhost varchar(31) DEFAULT NULL,
  prescond text
);

CREATE TABLE v_alias (
  eid integer NOT NULL,
  email_id varchar(127)   DEFAULT NULL,
  nickname varchar(127)  DEFAULT NULL,
  prescond text
);