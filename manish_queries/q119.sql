select *
       from store_sales
           ,date_dim
       where ss_sold_date_sk = d_date_sk
         and d_year between 2000 and 2000 + 2
;