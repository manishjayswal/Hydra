select *
    from catalog_sales, date_dim
          where catalog_sales.cs_sold_date_sk = date_dim.d_date_sk
      and d_month_seq between 1191 and 1191 + 11
  ;