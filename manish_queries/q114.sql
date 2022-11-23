select *
       from catalog_sales
           ,date_dim 
       where d_year = 1999 
         and d_moy = 6 
         and cs_sold_date_sk = d_date_sk 
;