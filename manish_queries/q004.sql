-- start query 7 in stream 0 using template query32.tpl
select *
from 
   catalog_sales 
   ,item 
   ,date_dim
where
i_manufact_id = 291
and i_item_sk = cs_item_sk 
and d_date between '2000-03-22' and '2000-06-22'
and d_date_sk = cs_sold_date_sk 
;
-- end query 7 in stream 0 using template query32.tpl