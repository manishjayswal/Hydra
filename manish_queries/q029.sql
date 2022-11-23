select *
          from store_sales,date_dim
          where 
                ss_sold_date_sk = d_date_sk and
                d_year = 2004 and
                d_moy between 3 and 3+2
                ;