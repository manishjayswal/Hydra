SELECT *
            FROM customer_address, customer
            WHERE ca_address_sk = c_current_addr_sk and
                  c_preferred_cust_flag='Y'
;
-- end query 63 in stream 0 using template query8.tpl