-- start query 77 in stream 0 using template query87.tpl
select *
       from store_sales, date_dim
       where store_sales.ss_sold_date_sk = date_dim.d_date_sk
         and d_month_seq between 1214 and 1214+11
;  