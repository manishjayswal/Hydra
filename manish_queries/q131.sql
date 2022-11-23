-- modifying q094.sql
-- start query 79 in stream 0 using template query73.tpl
select *
    from store_sales,date_dim,store,household_demographics
    where store_sales.ss_sold_date_sk = date_dim.d_date_sk
    and store_sales.ss_store_sk = store.s_store_sk  
    and store_sales.ss_hdemo_sk = household_demographics.hd_demo_sk
    and (household_demographics.hd_buy_potential = 'gt10000' or
         household_demographics.hd_buy_potential = 'from5001to10000')
    and (household_demographics.hd_vehicle_count > 0
      or household_demographics.hd_dep_count = 5)
    and date_dim.d_dom between 1 and 2
    and d_dow = 1
    and (store.s_county in ('Williamson County','Williamson County','Williamson County','Williamson County')
      or store.s_city in ('Midway','Fairview','Fairview','Fairview','Fairview')
	  or store.s_number_employees between 200 and 295)
;

-- end query 79 in stream 0 using template query73.tpl