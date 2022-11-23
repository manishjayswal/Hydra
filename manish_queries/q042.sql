select *
      from store_sales
      where ss_quantity between 16 and 20
        and (ss_list_price between 16 and 16+10
          or ss_coupon_amt between 13313 and 13313+1000
          or ss_wholesale_cost between 8 and 8+20)
;