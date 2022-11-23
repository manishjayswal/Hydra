-- start query 24 in stream 0 using template query62.tpl
select *
from
   web_sales
  ,date_dim
where
    d_month_seq between 1212 and 1212 + 11
and ws_ship_date_sk   = d_date_sk
;

-- end query 24 in stream 0 using template query62.tpl