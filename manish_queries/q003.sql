-- start query 5 in stream 0 using template query39.tpl
select *
      from inventory
          ,item
          ,warehouse
          ,date_dim
      where inv_item_sk = i_item_sk
        and inv_warehouse_sk = w_warehouse_sk
        and inv_date_sk = d_date_sk
        and d_year =1999
;

-- end query 5 in stream 0 using template query39.tpl