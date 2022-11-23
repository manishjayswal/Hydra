-- start query 80 in stream 0 using template query84.tpl
select *
 from customer
     ,customer_address
     ,household_demographics
     ,income_band
 where ca_city	        =  'Antioch'
   and c_current_addr_sk = ca_address_sk
   and ib_lower_bound   >=  9901
   and ib_upper_bound   <=  9901 + 50000
   and ib_income_band_sk = hd_income_band_sk
   and hd_demo_sk = c_current_hdemo_sk
 ;

-- end query 80 in stream 0 using template query84.tpl