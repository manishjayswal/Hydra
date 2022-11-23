select * 
            from catalog_sales,date_dim
            where 
                  cs_sold_date_sk = d_date_sk and
                  d_year = 2000 and
                  d_moy between 2 and 2+3
;
-- end query 26 in stream 0 using template query10.tpl