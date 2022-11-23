select *
      from store_sales
      where ss_quantity between 21 and 25
        and (ss_list_price between 153 and 153+10
          or ss_coupon_amt between 4490 and 4490+1000
          or ss_wholesale_cost between 14 and 14+20);