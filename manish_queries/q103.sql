select *
       from web_sales, date_dim
       where web_sales.ws_sold_date_sk = date_dim.d_date_sk
         and d_month_seq between 1214 and 1214+11
;

-- end query 77 in stream 0 using template query87.tpl