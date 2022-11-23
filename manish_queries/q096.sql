select *
 from store_returns,
      date_dim
 where sr_returned_date_sk = d_date_sk
       and d_date between '1998-08-14' and '1998-09-14'
 ;