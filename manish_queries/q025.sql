select *
            from web_sales,date_dim
            where 
                  ws_sold_date_sk = d_date_sk and
                  d_year = 2000 and
                  d_moy between 2 ANd 2+3
;