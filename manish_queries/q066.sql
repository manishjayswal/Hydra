select *
        from item
        where
        (i_category = 'Women' and 
        (i_color = 'olive' or i_color = 'grey') and 
        (i_units = 'Bundle' or i_units = 'Cup') and
        (i_size = 'petite' or i_size = 'small')
        ) or
        (i_category = 'Women' and
        (i_color = 'hot' or i_color = 'thistle') and
        (i_units = 'Box' or i_units = 'Each') and
        (i_size = 'large' or i_size = 'medium')
        ) or
        (i_category = 'Men' and
        (i_color = 'chiffon' or i_color = 'yellow') and
        (i_units = 'Carton' or i_units = 'Dozen') and
        (i_size = 'NA' or i_size = 'extra_large')
        ) or
        (i_category = 'Men' and
        (i_color = 'bisque' or i_color = 'turquoise') and
        (i_units = 'Case' or i_units = 'Tsp') and
        (i_size = 'petite' or i_size = 'small')
        );