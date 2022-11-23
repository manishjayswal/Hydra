-- start query 31 in stream 0 using template query37.tpl
select *
 from item, inventory, date_dim
 where i_current_price between 4 and 10
 and inv_item_sk = i_item_sk
 and d_date_sk=inv_date_sk
 and d_date between '2002-01-18' and '2002-03-18'
 and i_manufact_id in (744,691,853,946)
 and inv_quantity_on_hand between 100 and 500
 ;

-- end query 31 in stream 0 using template query37.tpl
