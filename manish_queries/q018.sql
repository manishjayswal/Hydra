select *
 from
 	catalog_sales,
 	date_dim,
         customer_address,
         item
where i_category in ('Home')
 and     cs_item_sk              = i_item_sk
 and     cs_sold_date_sk         = d_date_sk
 and     d_year                  = 2000
 and     d_moy                   = 2
 and     cs_bill_addr_sk         = ca_address_sk
 and     ca_gmt_offset           = -5 
;