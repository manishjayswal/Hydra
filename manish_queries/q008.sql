-- start query 13 in stream 0 using template query91.tpl
select  *
from
        catalog_returns,
        date_dim
where
	    cr_returned_date_sk     = d_date_sk
and     d_year                  = 2000 
and     d_moy                   = 12
;

-- end query 13 in stream 0 using template query91.tpl
-- first split