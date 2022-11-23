-- start query 97 in stream 0 using template query61.tpl
select *
   from  customer
        ,customer_address
   where ca_address_sk = c_current_addr_sk
   and   ca_gmt_offset = -6;
-- end query 97 in stream 0 using template query61.tpl
-- second split