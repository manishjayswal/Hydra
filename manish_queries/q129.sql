-- modifying q046.sql
-- start query 39 in stream 0 using template query66.tpl
select *
     from
          web_sales
         ,customer_address
         ,date_dim
         ,time_dim
 	  ,ship_mode
     where
            ws_sold_date_sk = d_date_sk
        and ws_sold_time_sk = t_time_sk
 	and ws_ship_mode_sk = sm_ship_mode_sk
 	and ws_ship_addr_sk = ca_address_sk
    and (d_year = 1999 or d_qoy = 2 or d_moy = 12)
 	and t_time between 46185 and 46185+28800 
 	and sm_carrier in ('DIAMOND','ZOUROS')
 	and     ca_gmt_offset           = -6
;
