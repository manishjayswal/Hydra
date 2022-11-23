select *
 from catalog_sales,
      date_dim
 where cs_sold_date_sk = d_date_sk
       and d_date between '1998-08-14' and '1998-09-14'
 ;