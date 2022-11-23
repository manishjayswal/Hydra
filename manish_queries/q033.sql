 select *
 from
 	catalog_sales,
 	date_dim,
         customer_address,
         item
where i_category in ('Children')
 and     cs_item_sk              = i_item_sk
 and     cs_sold_date_sk         = d_date_sk
 and     d_year                  = 1998
 and     d_moy                   = 8
 and     cs_bill_addr_sk         = ca_address_sk
 and     ca_gmt_offset           = -5 
;