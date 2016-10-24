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
#include	<ctype.h>

#include	"tooltool.h"

#include	<suntool/tty.h>

PUBLIC	Tty	tty;

PRIVATE	int	value_invalid = FALSE;
PRIVATE	struct	itimerval	timer_int;

/************************************************************************/
/* These routines deal with managing tooltool events			*/
/************************************************************************/

/************************************************************************/
PRIVATE	int	get_shifts(event)

Event	*event;

{	int	shifts = 0;

	if (event_shift_is_down(event))
	   shifts += S_SHIFT;
	if (event_ctrl_is_down(event))
	   shifts += S_CONTROL;
	if (event_meta_is_down(event))
	   shifts += S_META;
	return(shifts);
}

/************************************************************************/
PRIVATE	int	is_a_function_key(event)

Event	*event;

{
	return(event_is_key_left(event) || event_is_key_top(event) || event_is_key_right(event));
}

/************************************************************************/
PRIVATE	a_ptr	key_is_mapped(event)

Event	*event;

{	int	set, key;
	a_ptr	a;

	if (event_is_key_left(event)) {
	   set = LEFT_KEY_SET;
	   key = event_id(event) - KEY_LEFT(1);
	   }
	else if (event_is_key_top(event)) {
	   set = TOP_KEY_SET;
	   key = event_id(event) - KEY_TOP(1);
	   }
	else if (event_is_key_right(event)) {
	   set = RIGHT_KEY_SET;
	   key = event_id(event) - KEY_RIGHT(1);
	   }
	else
	   return(NULL);
	return(tt_func_keys[set][key][get_shifts(event)]);
}

/************************************************************************/
PRIVATE	timer_proc()

{
	if (tt_action_depth > 0)
	   tt_timer_pending = TRUE;
	else
	   tt_do_action(tt_timer_action);
}

/************************************************************************/
EXPORT	Panel_setting	notify_proc(item, event)

Panel_item	item;
Event		*event;

{	g_ptr	b;
	char	*p, buf[1024];
	int	i;
	cv_ptr	cv;

	b = (g_ptr) panel_get(item, PANEL_CLIENT_DATA);
	if (b->kind == GADGET_BUTTON)
	   tt_do_action(b->u.but.action[get_shifts(event)]);
	else if (b->kind == GADGET_TEXT) {
	   if (index(b->u.tex.completion, event_id(event))) {
	      p = (char *) panel_get(item, PANEL_VALUE);
	      if (p = (char *) expand_filename(p))
	         panel_set(item, PANEL_VALUE, p, 0);
	      else
	         window_bell(panel_get(item, PANEL_PARENT_PANEL));
	      }
	   else if (index(b->u.tex.trigger, event_id(event)))
	      tt_do_action(b->u.tex.action);
	   else if (event_id(event) == '\t')
	      if (event_shift_is_down(event))
	         panel_backup_caret(panel_get(item, PANEL_PARENT_PANEL));
	      else
	         panel_advance_caret(panel_get(item, PANEL_PARENT_PANEL));
	   else if (!index(b->u.tex.ignore, event_id(event)))
	      return(PANEL_INSERT);
	   return(PANEL_NONE);
	   }
	else if (b->kind == GADGET_CHOICE) {
	   i = (int) panel_get(item, PANEL_VALUE);
	   for (cv = b->u.cho.value; i && cv; i--, cv = cv->next)
	      ;
	   if (cv)
	      tt_do_action(cv->action);
	   }
	else if (b->kind == GADGET_SLIDER)
	   tt_do_action(b->u.sli.action);
}

/************************************************************************/
EXPORT	event_proc(item, event)

Panel_item	item;
Event		*event;

{	char	c;
	g_ptr	b;
	a_ptr	a;
	d_ptr	d;

	d = (d_ptr) window_get(panel_get(item, PANEL_PARENT_PANEL), WIN_CLIENT_DATA);
	b = (g_ptr) panel_get(item, PANEL_CLIENT_DATA);
	if (event_is_ascii(event) || event_is_meta(event))
	   if (d->text_items_exist || tt_normal_off)
	      if (b->kind == GADGET_TEXT && event_id(event) == '\t')
	         notify_proc(item, event);
	      else
	         panel_default_handle_event(item, event);
	   else {
	      c = event_id(event);
	      if (tty)
	         ttysw_input(tty, &c, 1);
	      }
	else if (is_a_function_key(event)) {
	   if (a = key_is_mapped(event)) {
	      if (event_is_down(event))
	         tt_do_action(a);
	      }
	   else if (!tt_function_off)
	      panel_default_handle_event(item, event);
	   }
	else { /* handle each panel item type separately */
	   if (b->kind == GADGET_BUTTON) {
	      if (event_is_down(event) && event_id(event) == MS_RIGHT)
	         tt_do_action(menu_show(b->u.but.menu, d->panel, event, 0));
	      else
	         panel_default_handle_event(item, event);
	      }
	   else if (b->kind == GADGET_MENU) {
	      if (event_is_down(event) && event_id(event) == MS_RIGHT) {
	         a = (a_ptr) menu_show(b->u.men.menu, d->panel, event, 0);
	         if (value_invalid)
	            value_invalid = FALSE;
	         else
	            tt_do_action(a);
	         }
	      else
	         panel_default_handle_event(item, event);
	      }
	   else
	      panel_default_handle_event(item, event);
	   }
}

/************************************************************************/
EXPORT	background_proc(panel, event)

Panel	panel;
Event	*event;

{	char	c;
	a_ptr	a;
	d_ptr	d;

	d = (d_ptr) window_get(panel, WIN_CLIENT_DATA);
	if (event_is_ascii(event) || event_is_meta(event))
	   if (d->text_items_exist || tt_normal_off)
	      panel_default_handle_event(panel, event);
	   else {
	      c = event_id(event);
	      if (tty)
	         ttysw_input(tty, &c, 1);
	      }
	else if (is_a_function_key(event)) {
	   if (a = key_is_mapped(event)) {
	      if (event_is_down(event))
	         tt_do_action(a);
	      }
	   else if (!tt_function_off)
	      panel_default_handle_event(panel, event);
	   }
	else
	   panel_default_handle_event(panel, event);
}

/************************************************************************/
PRIVATE	Notify_value	handle_mouse(button, shift, tty, event, arg, type)

int			button;
int			shift;
Tty			tty;
Event			*event;
Notify_arg		arg;
Notify_event_type	type;

{	int	x, y;
	a_ptr	a;

	if (tt_mouse_chars) {
	   x = event_x(event) / charwidth_of(tt_a_font) + tt_mouse_base;
	   y = event_y(event) / charheight_of(tt_a_font) + tt_mouse_base;
	   }
	else {
	   x = event_x(event) + tt_mouse_base;
	   y = event_y(event) + tt_mouse_base;
	   }
	if (tt_mouse[button][shift].defined == MOUSE_UNDEFINED)
	   return(notify_next_event_func(tty, event, arg, type));
	else if (tt_mouse[button][shift].defined == MOUSE_STRING)
	   a = tt_mouse[button][shift].action;
	else if (tt_mouse[button][shift].defined == MOUSE_MENU) {
	   a = (a_ptr) menu_show(tt_mouse[button][shift].menu, tty, event, 0);
	   if (value_invalid) {
	      a = NULL;
	      value_invalid = FALSE;
	      }
	   }
	tt_mouse_x->value->number = x;
	tt_mouse_y->value->number = y;
	tt_do_action(a);
	return(NOTIFY_DONE);
}

/************************************************************************/
EXPORT	Menu	ttymenu_proc(m, op)

Menu	m;
Menu_generate	op;

{
	value_invalid = TRUE;
	return(tt_ttymenu);
}

/************************************************************************/
EXPORT	Notify_value	close_proc(win, event, arg, type)

Window	win;
Event	*event;
Notify_arg	arg;
Notify_event_type	type;

{	int	init_closed, curr_closed;
	Notify_value	value;
	d_ptr	d;

	init_closed = (int) window_get(tt_base_window->frame, FRAME_CLOSED);
	value = notify_next_event_func(win, event, arg, type);
	curr_closed = (int) window_get(tt_base_window->frame, FRAME_CLOSED);
	if (init_closed != curr_closed)
	   if (curr_closed) { /* transition from open to closed */
	      tt_do_action(tt_base_window->close_action);
	      for (d = tt_base_window->next; d; d = d->next)
	         if (d->is_open)
	            window_set(d->frame, WIN_SHOW, FALSE, 0);
	      }
	   else { /* transition from closed to open */
	      tt_do_action(tt_base_window->open_action);
	      for (d = tt_base_window->next; d; d = d->next)
	         if (d->is_open)
	            window_set(d->frame, WIN_SHOW, TRUE, 0);
	      }
	return(value);
}

/************************************************************************/
EXPORT	Notify_value	tty_handler(tty, event, arg, type)

Tty			tty;
Event			*event;
Notify_arg		arg;
Notify_event_type	type;

{	a_ptr	a;

	if ((event_is_ascii(event) || event_is_meta(event)) && tt_normal_off)
	   return(NOTIFY_DONE);
	else if (is_a_function_key(event)) {
	   if (a = key_is_mapped(event)) {
	      if (event_is_down(event))
	         tt_do_action(a);
	      }
	   else if (!tt_function_off)
	      return(close_proc(tty, event, arg, type));
	   return(NOTIFY_DONE);
	   }
	else if (event_id(event) == MS_LEFT && event_is_down(event))
	   return(handle_mouse(MOUSE_LEFT, get_shifts(event), tty, event, arg, type));
	else if (event_id(event) == MS_MIDDLE && event_is_down(event))
	   return(handle_mouse(MOUSE_CENTER, get_shifts(event), tty, event, arg, type));
	else if (event_id(event) == MS_RIGHT && event_is_down(event))
	   return(handle_mouse(MOUSE_RIGHT, get_shifts(event), tty, event, arg, type));
	else
	   return(close_proc(tty, event, arg, type));
}

/************************************************************************/
EXPORT	Notify_value	tt_dialog_done(frame)

Frame	frame;

{	d_ptr	d;

	d = (d_ptr) window_get(frame, WIN_CLIENT_DATA);
	d->is_open = FALSE;
	tt_do_action(d->close_action);
	window_set(frame, WIN_SHOW, FALSE, 0);
	return(NOTIFY_DONE);
}

/************************************************************************/
EXPORT	tt_set_timer(sec, usec)

int	sec;
int	usec;

{
	if (sec != 0 || usec != 0) {
	   timer_int.it_value.tv_sec = timer_int.it_interval.tv_sec = sec;
	   timer_int.it_value.tv_usec = timer_int.it_interval.tv_usec = usec;
	   notify_set_itimer_func(tt_base_window->frame, timer_proc, ITIMER_REAL, &timer_int, NULL);
	   }
	else
	   notify_set_itimer_func(tt_base_window->frame, timer_proc, ITIMER_REAL, NULL, NULL);
}
