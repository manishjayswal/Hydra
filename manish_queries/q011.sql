-- start query 15 in stream 0 using template query43.tpl
select *
 from date_dim, store_sales, store
 where d_date_sk = ss_sold_date_sk and
       s_store_sk = ss_store_sk and
       s_gmt_offset = -5 and
       d_year = 2000 
 ;

-- end query 15 in stream 0 using template query43.tpl