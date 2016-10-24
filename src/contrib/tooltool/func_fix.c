/************************************************************************/
/*	Copyright 1988 by Chuck Musciano and Harris Corporation		*/
/*									*/
/*	Permission to use, copy, modify, and distribute this software	*/
/*	and its documentation for any purpose and without fee is	*/
/*	hereby granted, provided that the above copyright notice	*/
/*	appear in all copies and that both that copyright notice and	*/
/*	this permission notice appear in supporting documentation, and	*/
/*	that the name of Chuck Musciano and Harris Corporation not be	*/
/*	used in advertising or publicity pertaining to distribution	*/
/*	of the software without specific, written prior permission.	*/
/*	Chuck Musciano and Harris Corporation make no representations	*/
/*	about the suitability of this software for any purpose.  It is	*/
/*	provided "as is" without express or implied warranty.		*/
/************************************************************************/

#include	<stdio.h>

#include	"tooltool.h"

#define		advance_queue_ptr(q)	((q) = ((q) + 1) % MAX_EVENTS)

#define		MAX_EVENTS		16

typedef	struct	fk_data	fk_rec, *fk_ptr;

struct	fk_data	{int	candidate;
		 int	true_event;
		 char	*expansion;
		};

PRIVATE	Event	event_queue[MAX_EVENTS];
PRIVATE	Event	saved_event[MAX_EVENTS];
PRIVATE	int	queue_head = 0;
PRIVATE	int	queue_tail = 0;
PRIVATE	int	state = 0;

PRIVATE	fk_rec	func_key[] = {{TRUE, KEY_LEFT(2),   "\033[193z"},
			      {TRUE, KEY_LEFT(3),   "\033[194z"},
			      {TRUE, KEY_LEFT(4),   "\033[195z"},
			      {TRUE, KEY_LEFT(5),   "\033[196z"},
			      {TRUE, KEY_LEFT(6),   "\033[197z"},
			      {TRUE, KEY_LEFT(7),   "\033[198z"},
			      {TRUE, KEY_LEFT(8),   "\033[199z"},
			      {TRUE, KEY_LEFT(9),   "\033[200z"},
			      {TRUE, KEY_LEFT(10),  "\033[201z"},
			      {TRUE, KEY_TOP(1),    "\033[224z"},
			      {TRUE, KEY_TOP(2),    "\033[225z"},
			      {TRUE, KEY_TOP(3),    "\033[226z"},
			      {TRUE, KEY_TOP(4),    "\033[227z"},
			      {TRUE, KEY_TOP(5),    "\033[228z"},
			      {TRUE, KEY_TOP(6),    "\033[229z"},
			      {TRUE, KEY_TOP(7),    "\033[230z"},
			      {TRUE, KEY_TOP(8),    "\033[231z"},
			      {TRUE, KEY_TOP(9),    "\033[232z"},
			      {TRUE, KEY_RIGHT(1),  "\033[208z"},
			      {TRUE, KEY_RIGHT(2),  "\033[209z"},
			      {TRUE, KEY_RIGHT(3),  "\033[210z"},
			      {TRUE, KEY_RIGHT(4),  "\033[211z"},
			      {TRUE, KEY_RIGHT(5),  "\033[212z"},
			      {TRUE, KEY_RIGHT(6),  "\033[213z"},
			      {TRUE, KEY_RIGHT(7),  "\033[214z"},
			      {TRUE, KEY_RIGHT(8),  "\033[215z"},
			      {TRUE, KEY_RIGHT(9),  "\033[216z"},
			      {TRUE, KEY_RIGHT(10), "\033[217z"},
			      {TRUE, KEY_RIGHT(11), "\033[218z"},
			      {TRUE, KEY_RIGHT(12), "\033[219z"},
			      {TRUE, KEY_RIGHT(13), "\033[220z"},
			      {TRUE, KEY_RIGHT(14), "\033[221z"},
			      {TRUE, KEY_RIGHT(15), "\033[222z"},
			      {NULL, NULL,          NULL}};

/************************************************************************/
PRIVATE	enqueue_event(event)

Event	*event;

{
	event_queue[queue_head] = *event;
	if (advance_queue_ptr(queue_head) == queue_tail)
	   abend("internal event queue overflow");
}

/************************************************************************/
PRIVATE	Event	*dequeue_event()

{	Event	*result;

	if (queue_tail == queue_head)
	   return(NULL);
	result = &(event_queue[queue_tail]);
	advance_queue_ptr(queue_tail);
	return(result);
}

/************************************************************************/
PRIVATE	reset_state_machine(enqueue_events)

int	enqueue_events;

{	int	i;

	if (enqueue_events)
	   for (i = 0; i < state; i++)
	      enqueue_event(&(saved_event[i]));
	for (i = 0; func_key[i].expansion; i++)
	   func_key[i].candidate = TRUE;
	state = 0;
}

/************************************************************************/
PRIVATE	advance_state_machine(event)

register	Event	*event;

{	register	int	candidates;
	register	fk_ptr	last_match, key;

	for (key = func_key, candidates = 0; key->expansion; key++)
	   if (key->candidate && key->expansion[state] == event_id(event)) {
	      candidates++;
	      last_match = key;
	      }
	   else
	      key->candidate = FALSE;
	if (candidates == 0) {
	   reset_state_machine(TRUE);
	   enqueue_event(event);
	   }
	else if (candidates == 1 && last_match->expansion[state + 1] == '\0') {
	   event_set_id(event, last_match->true_event);
	   reset_state_machine(FALSE);
	   enqueue_event(event);
	   }
	else {
	   saved_event[state] = *event;
	   if (++state >= MAX_EVENTS)
	      abend("oveflowed internal event buffer");
	   }
}

/************************************************************************/
PRIVATE	Notify_value	function_check(win, event, arg, type)

Window	win;
Event	*event;
Notify_arg	arg;
Notify_event_type	type;

{	Notify_value	result;

	if (event_is_ascii(event) || event_is_meta(event))
	   if (event_is_down(event))
	      advance_state_machine(event);
	   else
	      reset_state_machine(TRUE);
	else {
	   reset_state_machine(TRUE);
	   enqueue_event(event);
	   }
	while (event = dequeue_event())
	   if ((result = notify_next_event_func(win, event, arg, type)) != NOTIFY_DONE)
	      return(result);
	return(NOTIFY_DONE);
}

/************************************************************************/
EXPORT	init_function_fix(win)

Window	win;

{
	window_set(win, WIN_CONSUME_KBD_EVENT,  WIN_UP_ASCII_EVENTS, 0);
	notify_interpose_event_func(win, function_check, NOTIFY_SAFE);
}
