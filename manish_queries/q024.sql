select *
from store_sales,date_dim
where ss_sold_date_sk = d_date_sk and
d_year = 2000 and
d_moy between 2 and 2+3
;
