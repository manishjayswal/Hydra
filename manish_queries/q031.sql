select * 
            from catalog_sales,date_dim
            where 
                  cs_sold_date_sk = d_date_sk and
                  d_year = 2004 and
                  d_moy between 3 and 3+2
 ;

-- end query 28 in stream 0 using template query69.tpl