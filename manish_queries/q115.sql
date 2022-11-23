select *
       from web_sales 
           ,date_dim 
       where d_year = 1999 
         and d_moy = 6 
         and ws_sold_date_sk = d_date_sk 
;

-- end query 68 in stream 0 using template query23.tpl