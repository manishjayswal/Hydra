-- start query 14 in stream 0 using template query21.tpl
select *
   from inventory
       ,warehouse
       ,item
       ,date_dim
   where i_current_price between 0.99 and 1.49
     and i_item_sk          = inv_item_sk
     and inv_warehouse_sk   = w_warehouse_sk
     and inv_date_sk    = d_date_sk
     and d_date between '2001-02-14' and '2001-05-14'
;

-- end query 14 in stream 0 using template query21.tpl