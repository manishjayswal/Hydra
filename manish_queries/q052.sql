-- start query 44 in stream 0 using template query92.tpl
select * 
from 
    web_sales 
   ,item 
   ,date_dim
where
i_manufact_id = 248
and i_item_sk = ws_item_sk 
and d_date between '2000-02-02' and '2000-05-02'
and d_date_sk = ws_sold_date_sk 
;

-- end query 44 in stream 0 using template query92.tpl