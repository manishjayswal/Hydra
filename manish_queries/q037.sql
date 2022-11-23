-- start query 34 in stream 0 using template query70.tpl
select *
 from
    store_sales
   ,date_dim       d1
 where
    d1.d_month_seq between 1181 and 1181+11
 and d1.d_date_sk = ss_sold_date_sk
 ;

-- end query 34 in stream 0 using template query70.tpl