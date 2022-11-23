-- start query 18 in stream 0 using template query45.tpl
select *
 from web_sales, date_dim
 where ws_sold_date_sk = d_date_sk
 	and d_qoy = 2 and d_year = 1999
 ;