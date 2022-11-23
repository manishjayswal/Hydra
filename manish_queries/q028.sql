-- start query 28 in stream 0 using template query69.tpl
select *
 from
  customer c,customer_address ca
 where
  c.c_current_addr_sk = ca.ca_address_sk and
  ca_state in ('SD','KY','MO')
  ;
   