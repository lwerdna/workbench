#!/usr/bin/env python

from mortgage import Loan

loan = Loan(principal=200000, interest=.03, term=15)

print('{:>4}  {:>10s} {:>10s} {:>10s} {:>10s}'.format('', 'payment', 'interest', 'principal', 'remaining'))
print('{:>4}  {:>10s} {:>10s} {:>10s} {:>10s}'.format('', '-------', '--------', '---------', '---------'))

for installment in loan.schedule():
	print('{:>4}: {:>10.02f} {:>10.02f} {:>10.02f} {:>10.02f}'.format(
		installment.number, installment.payment, installment.interest, installment.principal, installment.balance))

loan.summarize
