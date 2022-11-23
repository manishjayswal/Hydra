select *
 from web_sales
     ,date_dim
 where ws_sold_date_sk = d_date_sk
   and d_year in (1998,1998+1)
;

-- end query 76 in stream 0 using template query74.tpl