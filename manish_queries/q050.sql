-- start query 42 in stream 0 using template query47.tpl
 select *
 from item, store_sales, date_dim
 where ss_item_sk = i_item_sk and
       ss_sold_date_sk = d_date_sk and
       (
         d_year = 2000 or
         ( d_year = 2000-1 and d_moy =12) or
         ( d_year = 2000+1 and d_moy =1)
       )
 ;

-- end query 42 in stream 0 using template query47.tpl