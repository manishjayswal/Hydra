-- start query 97 in stream 0 using template query61.tpl
select *
   from  store_sales
        ,store
        ,promotion
        ,date_dim
        ,item
   where ss_sold_date_sk = d_date_sk
   and   ss_store_sk = s_store_sk
   and   ss_promo_sk = p_promo_sk
   and   ss_item_sk = i_item_sk 
   and   i_category = 'Electronics'
   and   (p_channel_dmail = 'Y' or p_channel_email = 'Y' or p_channel_tv = 'Y')
   and   s_gmt_offset = -5
   and   d_year = 2000
   and   d_moy  = 11;
-- end query 97 in stream 0 using template query61.tpl
-- first split