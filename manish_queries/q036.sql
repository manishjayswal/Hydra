-- start query 32 in stream 0 using template query98.tpl
select *
from	
	store_sales
    	,item 
    	,date_dim
where 
	ss_item_sk = i_item_sk 
  	and i_category in ('Music', 'Jewelry', 'Women')
  	and ss_sold_date_sk = d_date_sk
	and d_date between '1999-04-26' and '1999-05-26'
;

-- end query 32 in stream 0 using template query98.tpl