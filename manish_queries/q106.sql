-- start query 75 in stream 0 using template query30.tpl
select *
 from web_returns
     ,date_dim
 where wr_returned_date_sk = d_date_sk 
   and d_year =2000 
;

-- end query 75 in stream 0 using template query30.tpl