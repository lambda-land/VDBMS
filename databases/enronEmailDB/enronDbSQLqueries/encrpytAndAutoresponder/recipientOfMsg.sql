-- | show the recipient of the message 9138
select *
from v_message 
inner join recipientinfo on v_message.mid = recipientinfo.mid
where v_message.mid = 9138

