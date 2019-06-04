-- CREATE TABLE mailhost (
--     did int NOT NULL AUTO_INCREMENT,
--     eid int,
--     username varchar(31) ,
--     PRIMARY KEY (did)
-- );

-- INSERT INTO mailhost (username,eid)
-- SELECT username,eid
-- FROM mailhost_view



-- select emp.*,username,mail.did
-- from mailhost mail
--  inner join v_employee emp
--  on mail.eid = emp.eid
--  order by emp.did
 
update v_employee 
inner join mailhost 
on v_employee.eid = mailhost.eid 
set v_employee.did = mailhost.did
where v_employee.did is null -- and other conditions you might want


