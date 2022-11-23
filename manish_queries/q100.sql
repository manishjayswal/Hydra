 select *
 from web_returns,
      date_dim
 where wr_returned_date_sk = d_date_sk
       and d_date between '1998-08-14' and '1998-09-14'
;

-- end query 78 in stream 0 using template query77.tpl