-- start query 72 in stream 0 using template query71.tpl

select * 
                 from web_sales,date_dim
                 where d_date_sk = ws_sold_date_sk
                   and d_moy=12
                   and d_year=2002
;
