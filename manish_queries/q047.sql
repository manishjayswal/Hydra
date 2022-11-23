select *
     from
          catalog_sales
         ,date_dim
         ,time_dim
 	 ,ship_mode
     where
            cs_sold_date_sk = d_date_sk
        and cs_sold_time_sk = t_time_sk
 	and cs_ship_mode_sk = sm_ship_mode_sk
        and d_year = 1999
 	and t_time between 46185 AND 46185+28800 
 	and sm_carrier in ('DIAMOND','ZOUROS')
 ;

-- end query 39 in stream 0 using template query66.tpl