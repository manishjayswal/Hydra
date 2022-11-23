select *
      from store_sales
      where ss_quantity between 6 and 10
        and (ss_list_price between 135 and 135+10
          or ss_coupon_amt between 3897 and 3897+1000
          or ss_wholesale_cost between 79 and 79+20);