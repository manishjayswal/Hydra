-- start query 64 in stream 0 using template query12.tpl
select *
from	
	web_sales
    	,item 
    	,date_dim
where 
	ws_item_sk = i_item_sk 
  	and i_category in ('Children', 'Sports', 'Music')
  	and ws_sold_date_sk = d_date_sk
	and d_date between '2002-04-01' and '2002-05-01'
;

-- end query 64 in stream 0 using template query12.tpl