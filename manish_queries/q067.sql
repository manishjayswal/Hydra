 select *
        from item
        where       
       (i_category = 'Women' and 
        (i_color = 'chocolate' or i_color = 'lemon') and 
        (i_units = 'Unknown' or i_units = 'Oz') and
        (i_size = 'petite' or i_size = 'small')
        ) or
        (i_category = 'Women' and
        (i_color = 'light' or i_color = 'ivory') and
        (i_units = 'Ounce' or i_units = 'Ton') and
        (i_size = 'large' or i_size = 'medium')
        ) or
        (i_category = 'Men' and
        (i_color = 'rose' or i_color = 'sandy') and
        (i_units = 'Pound' or i_units = 'Lb') and
        (i_size = 'NA' or i_size = 'extra_large')
        ) or
        (i_category = 'Men' and
        (i_color = 'wheat' or i_color = 'burnished') and
        (i_units = 'Dram' or i_units = 'Pallet') and
        (i_size = 'petite' or i_size = 'small')
        )
 ;
