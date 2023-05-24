.thumb
.syntax unified

.globl _start
.globl test_it
.globl test_itt
.globl test_ite
.globl test_ittt
.globl test_itte
.globl test_itet
.globl test_itee
.globl test_itttt
.globl test_ittte
.globl test_ittet
.globl test_ittee
.globl test_itett
.globl test_itete
.globl test_iteet
.globl test_iteee
.globl lost_dataflow_return_value

.text

.thumb_func
_start:
	mov		pc, lr

/* one code */

.thumb_func
test_it:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	it		lt
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

	/* two codes */
.thumb_func
test_itt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itt		lt
	movlt	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ite:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ite		lt
	movlt	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

/* three codes */
.thumb_func
test_ittt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittt	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itte:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itte	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itet	lt
	movlt	%r0, #1
	movge	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itee	lt
	movlt	%r0, #1
	movge	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

/* four codes */
.thumb_func
test_itttt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itttt	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movlt	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittte:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittte	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movlt	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittet	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movge	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittee	lt
	movlt	%r0, #1
	movlt	%r0, #1
	movge	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itett:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itett	lt
	movlt	%r0, #1
	movge	%r0, #1
	movlt	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itete:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itete	lt
	movlt	%r0, #1
	movge	%r0, #1
	movlt	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_iteet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	iteet	lt
	movlt	%r0, #1
	movge	%r0, #1
	movge	%r0, #1
	movlt	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_iteee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	iteee	lt
	movlt	%r0, #1
	movge	%r0, #1
	movge	%r0, #1
	movge	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
lost_dataflow_return_value:
	push	{r7, lr}
	add		r7, sp, #0

	cmp		%r0, #0
	ite		lt
	movlt	%r8, #1
	movge	%r8, #2

	mov		%r0, %r8

	mov		sp, r7
	pop		{r7, pc}
