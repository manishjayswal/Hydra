-- start query 76 in stream 0 using template query74.tpl

 select *
 from store_sales
     ,date_dim
 where ss_sold_date_sk = d_date_sk
   and d_year in (1998,1998+1)
 ;