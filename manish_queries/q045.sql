-- start query 38 in stream 0 using template query97.tpl

select *
from store_sales,date_dim
where ss_sold_date_sk = d_date_sk
  and d_month_seq between 1202 and 1202 + 11
;

-- end query 38 in stream 0 using template query97.tpl