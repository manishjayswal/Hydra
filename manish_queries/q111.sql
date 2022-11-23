-- start query 71 in stream 0 using template query65.tpl

select  *
 		from store_sales, date_dim
 		where ss_sold_date_sk = d_date_sk and d_month_seq between 1223 and 1223+11
;

-- end query 71 in stream 0 using template query65.tpl