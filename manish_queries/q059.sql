select *
    from web_sales, date_dim
          where web_sales.ws_sold_date_sk = date_dim.d_date_sk
      and d_month_seq between 1191 and 1191 + 11
;

-- end query 54 in stream 0 using template query38.tpl