-- modifying q066.sql
select *
        from item
        where
        (
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
        )
        )
        or
        (
	    (i_category in ('Books','Children','Electronics')
	    and i_class in ('personal','portable','refernece','self-help')
	    and i_brand in ('scholaramalgamalg #14', 'scholaramalgamalg #7', 'exportiunivamalg #9', 'scholaramalgamalg #9')
	    )
	    or
	    (i_category in ('Women','Music','Men')
	    and i_class in ('accessories','classical','fragrances','pants')
	    and i_brand in ('amalgimporto #1', 'edu packscholar #1',' exportiimporto #1', 'importoamalg #1')
	    )
	    )
	    or
	    (i_current_price between 0.99 and 1.49)
	    or
	    i_manufact_id in (744,691,853,946)
	    or
	    i_manager_id=91
	    ;
	    