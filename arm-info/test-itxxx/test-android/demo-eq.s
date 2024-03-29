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
	it		eq
	moveq	%r0, #1
	mov		sp, r7
	pop		{r7, pc}

	/* two codes */
.thumb_func
test_itt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itt		eq
	moveq	%r0, #1
	moveq	%r0, #2
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ite:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ite		eq
	moveq	%r0, #1
	movne	%r0, #2
	mov		sp, r7
	pop		{r7, pc}

/* three codes */
.thumb_func
test_ittt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittt	eq
	moveq	%r0, #1
	moveq	%r0, #2
	moveq	%r0, #3
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itte:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itte	eq
	moveq	%r0, #1
	moveq	%r0, #2
	movne	%r0, #3
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itet	eq
	moveq	%r0, #1
	movne	%r0, #2
	moveq	%r0, #3
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itee	eq
	moveq	%r0, #1
	movne	%r0, #2
	movne	%r0, #3
	mov		sp, r7
	pop		{r7, pc}

/* four codes */
.thumb_func
test_itttt:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itttt	eq
	moveq	%r0, #1
	moveq	%r0, #2
	moveq	%r0, #3
	moveq	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittte:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittte	eq
	moveq	%r0, #1
	moveq	%r0, #2
	moveq	%r0, #3
	movne	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittet	eq
	moveq	%r0, #1
	moveq	%r0, #2
	movne	%r0, #3
	moveq	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_ittee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	ittee	eq
	moveq	%r0, #1
	moveq	%r0, #2
	movne	%r0, #3
	movne	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itett:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itett	eq
	moveq	%r0, #1
	movne	%r0, #2
	moveq	%r0, #3
	moveq	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_itete:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	itete	eq
	moveq	%r0, #1
	movne	%r0, #2
	moveq	%r0, #3
	movne	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_iteet:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	iteet	eq
	moveq	%r0, #1
	movne	%r0, #2
	movne	%r0, #3
	moveq	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
test_iteee:
	push	{r7, lr}
	add		r7, sp, #0
	cmp		%r0, #0
	iteee	eq
	moveq	%r0, #1
	movne	%r0, #2
	movne	%r0, #3
	movne	%r0, #4
	mov		sp, r7
	pop		{r7, pc}

.thumb_func
lost_dataflow_return_value:
	push	{r7, lr}
	add		r7, sp, #0

	cmp		%r0, #0
	ite		eq
	moveq	%r8, #1
	movne	%r8, #2

	mov		%r0, %r8

	mov		sp, r7
	pop		{r7, pc}
