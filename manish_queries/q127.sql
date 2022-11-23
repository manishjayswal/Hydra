-- modifying q084.sql
-- start query 90 in stream 0 using template query18.tpl
 select *
 from catalog_sales, customer_demographics, customer, customer_address, promotion
 where 
       cs_bill_cdemo_sk = cd_demo_sk and
       cs_bill_customer_sk = c_customer_sk and
       cs_promo_sk = p_promo_sk and
       cd_gender = 'F' and 
       cd_marital_status = 'D' and
   cd_education_status = '4 yr Degree' and
   c_current_addr_sk = ca_address_sk and
   c_birth_month in (6,5,12,4,3,7) and
   (p_channel_email = 'N' or p_channel_event = 'N') and
   ca_state in ('TN','IL','GA'
               ,'MO','CO','OH','NM')
 ;

-- end query 90 in stream 0 using template query18.tpl
