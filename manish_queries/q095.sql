-- start query 78 in stream 0 using template query77.tpl
select *
 from store_sales,
      date_dim
 where ss_sold_date_sk = d_date_sk
       and d_date between '1998-08-14' and '1998-09-14' 
 ;