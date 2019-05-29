CREATE 
    ALGORITHM = UNDEFINED 
    DEFINER = `root`@`localhost` 
    SQL SECURITY DEFINER
VIEW `message_view_useindex` AS
    SELECT 
        `msg`.`mid` AS `mid`,
        `msg`.`sender` AS `sender`,
        `msg`.`date` AS `date`,
        `msg`.`message_id` AS `message_id`,
        `msg`.`subject` AS `subject`,
        `msg`.`body` AS `body`,
        `msg`.`folder` AS `folder`,
        (CASE
            WHEN ISNULL(`emp`.`sign`) THEN FALSE
            WHEN (`emp`.`sign` IS NOT NULL) THEN TRUE
        END) AS `is_sign`,
        (CASE
            WHEN
                ((`emp`.`public_key` IS NOT NULL)
                    AND (`rec`.`public_key` IS NOT NULL))
            THEN
                TRUE
            ELSE FALSE
        END) AS `is_encrypt`
    FROM
        ((`message` `msg`
        JOIN `v_employee` `emp` ON ((`emp`.`Email_id` = `msg`.`sender`)))
        JOIN `recipientpublickeytable` `rec` ON ((`rec`.`mid` = `msg`.`mid`)))