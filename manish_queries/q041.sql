select *
      from store_sales
      where ss_quantity between 11 and 15
        and (ss_list_price between 106 and 106+10
          or ss_coupon_amt between 10740 and 10740+1000
          or ss_wholesale_cost between 16 and 16+20);