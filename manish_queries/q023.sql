-- start query 26 in stream 0 using template query10.tpl
select *
 from
  customer c,customer_address ca
 where
  c.c_current_addr_sk = ca.ca_address_sk and
  ca_county in ('Yellowstone County','Montgomery County','Divide County','Cedar County','Manassas Park city')
;
