-- start query 17 in stream 0 using template query94.tpl
select *
from
   web_sales ws1
  ,date_dim
  ,customer_address
  ,web_site
where
    d_date between '2002-4-01' and '2002-6-01'
and ws1.ws_ship_date_sk = d_date_sk
and ws1.ws_ship_addr_sk = ca_address_sk
and ca_state = 'MN'
and ws1.ws_web_site_sk = web_site_sk
and web_company_name = 'pri'
;

-- end query 17 in stream 0 using template query94.tpl