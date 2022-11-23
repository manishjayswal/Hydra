-- start query 94 in stream 0 using template query99.tpl
select * 
from
   catalog_sales
  ,date_dim
where
    d_month_seq between 1183 and 1183 + 11
and cs_ship_date_sk   = d_date_sk
;

-- end query 94 in stream 0 using template query99.tpl