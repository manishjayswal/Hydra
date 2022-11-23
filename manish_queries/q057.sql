-- start query 54 in stream 0 using template query38.tpl
select *
    from store_sales, date_dim
          where store_sales.ss_sold_date_sk = date_dim.d_date_sk
      and d_month_seq between 1191 and 1191 + 11
;