-- start query 12 in stream 0 using template query1.tpl
select *
from store_returns
,date_dim
where sr_returned_date_sk = d_date_sk
and d_year =1998
;

-- end query 12 in stream 0 using template query1.tpl