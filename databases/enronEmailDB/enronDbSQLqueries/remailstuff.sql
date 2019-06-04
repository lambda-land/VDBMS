
-- create view remail_view as 
-- SELECT eid,  concat(substring('ABCDEFGHIJKLMNOPQRSTUVWXYZ', rand()*26+1, 1),
--               substring('abcdelhio', rand()*9+1, 1),
--               substring('abcdelhio', rand()*9+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1),
--               substring('abcdefghijklmnopqrstuvwxyz', rand()*26+1, 1)
--              ) as pseudonym
-- FROM v_employee
-- where eid >=125
-- order by eid

create table v_remail_msg as 
select * from remail_view 



