theorem LOC {
   sum(for file in find(name="*.lu") then open(file).count("\n")) < 1000
}

To support development and documentation, please consider making a [donation](https://www.paypal.com/cgi-bin/webscr?cmd=_donations&business=7LYJV46P6WPAA&lc=US&item_name=Luck%20Software%20Foundation&currency_code=USD&bn=PP%2dDonationsBF%3abtn_donateCC_LG%2egif%3aNonHostedGuest).
