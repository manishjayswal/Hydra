-- start query 47 in stream 0 using template query35.tpl

select *
          from store_sales,date_dim
          where 
                ss_sold_date_sk = d_date_sk and
                d_year = 2001 and
                d_qoy < 4;