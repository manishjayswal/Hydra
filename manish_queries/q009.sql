-- start query 13 in stream 0 using template query91.tpl
select  *
from
        customer,
        customer_address,
        customer_demographics
where
        cd_demo_sk              = c_current_cdemo_sk
and     ca_address_sk           = c_current_addr_sk
and     ( (cd_marital_status       = 'M' and cd_education_status     = 'Unknown')
        or(cd_marital_status       = 'W' and cd_education_status     = 'Advanced Degree'))
and     ca_gmt_offset           = -6
;


-- end query 13 in stream 0 using template query91.tpl
-- second split