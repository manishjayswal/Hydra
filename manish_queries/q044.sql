select *
      from store_sales
      where ss_quantity between 26 and 30
        and (ss_list_price between 111 and 111+10
          or ss_coupon_amt between 8115 and 8115+1000
          or ss_wholesale_cost between 35 and 35+20)
;

-- end query 36 in stream 0 using template query28.tpl