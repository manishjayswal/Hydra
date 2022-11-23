 select *
 from
 	web_sales,
 	date_dim,
         customer_address,
         item
 where ws_item_sk              = i_item_sk
 and     ws_sold_date_sk         = d_date_sk
 and     d_year                  = 1998
 and     d_moy                   = 1
 and     ws_bill_addr_sk         = ca_address_sk
 and     ca_gmt_offset           = -5
 ;

-- end query 83 in stream 0 using template query56.tpl