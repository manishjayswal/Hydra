-- start query 70 in stream 0 using template query57.tpl
 select *
 from item, catalog_sales, date_dim
 where cs_item_sk = i_item_sk and
       cs_sold_date_sk = d_date_sk and
       (
         d_year = 1999 or
         ( d_year = 1999-1 and d_moy =12) or
         ( d_year = 1999+1 and d_moy =1)
       )
 ;

-- end query 70 in stream 0 using template query57.tpl