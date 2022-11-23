select *
       from store_sales
           ,item
           ,date_dim
       where ss_item_sk = i_item_sk
         and ss_sold_date_sk = d_date_sk
         and d_year = 2000+2 
         and d_moy = 11
;