-- start query 8 in stream 0 using template query19.tpl
select *
 from date_dim, store_sales, item
 where d_date_sk = ss_sold_date_sk
   and ss_item_sk = i_item_sk
   and i_manager_id=91
   and d_moy=12
   and d_year=2002 
 ;

-- end query 8 in stream 0 using template query19.tpl