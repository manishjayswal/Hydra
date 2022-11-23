-- start query 36 in stream 0 using template query28.tpl
select *
      from store_sales
      where ss_quantity between 0 and 5
        and (ss_list_price between 51 and 51+10 
             or ss_coupon_amt between 12565 and 12565+1000
             or ss_wholesale_cost between 52 and 52+20);