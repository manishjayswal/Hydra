-- start query 55 in stream 0 using template query22.tpl
select *
       from inventory
           ,date_dim
           ,item
           ,warehouse
       where inv_date_sk=d_date_sk
              and inv_item_sk=i_item_sk
              and inv_warehouse_sk = w_warehouse_sk
              and d_month_seq between 1199 and 1199 + 11
;

-- end query 55 in stream 0 using template query22.tpl