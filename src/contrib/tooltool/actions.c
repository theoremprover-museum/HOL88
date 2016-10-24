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

/************************************************************************/
PRIVATE	send_text(p)

char	*p;

{	int	len, sent;

	if (tty)
	   if (p && *p)
	      for (len = strlen(p), sent = 0; sent < len; )
	         sent += ttysw_input(tty, p + sent, len - sent);
}

/************************************************************************/
PRIVATE	do_open()

{	d_ptr	d;

	window_set(tt_base_window->frame, FRAME_CLOSED, FALSE, 0);
	for (d = tt_base_window->next; d; d = d->next)
	   if (d->is_open)
	window_set(d->frame, WIN_SHOW, TRUE, 0);
}

/************************************************************************/
PRIVATE	do_close()

{	d_ptr	d;

	window_set(tt_base_window->frame, FRAME_CLOSED, TRUE, 0);
	for (d = tt_base_window->next; d; d = d->next)
	   if (d->is_open)
	window_set(d->frame, WIN_SHOW, FALSE, 0);
}

/************************************************************************/
EXPORT	a_ptr	tt_make_action(op, arg1, arg2, arg3, arg4)

int	op;
e_ptr	arg1, arg2, arg3, arg4;

{	a_ptr	a;

	a = (a_ptr) safe_malloc(sizeof(a_data));
	a->next = NULL;
	switch (a->op = op) {
	   case BEEP_OP     :
	   case BREAK_OP    :
	   case CLOSE_OP    :
	   case CONTINUE_OP :
	   case EXIT_OP     :
	   		      break;
	   case DISPLAY_OP  : 
	   case EXPR_OP     :
	   case POPUP_OP    :
	   case REMOVE_OP   :
	   case SEND_OP     : a->expr = arg1;
	   		      break;
	   case FOR_OP      : a->init = arg1;
	   		      a->expr = arg2;
	   		      a->term = arg3;
	   		      a->body = (a_ptr) arg4;
	   		      break;
	   case IF_OP       : a->expr = arg1;
	   		      a->body = (a_ptr) arg2;
	   		      a->else_part = (a_ptr) arg3;
	   		      break;
	   case WHILE_OP    : a->expr = arg1;
	   		      a->body = (a_ptr) arg2;
	   		      break;
	   }
	return(a);
}

/************************************************************************/
EXPORT	tt_do_action(a)

a_ptr	a;

{	d_ptr	d;
	static	int	in_a_popup = FALSE, exit_pending = FALSE, close_pending = FALSE, open_pending = FALSE;
	static	int	break_pending = FALSE, continue_pending = FALSE;

	tt_action_depth++;
	for ( ; a && !break_pending && !continue_pending; a = a->next) {
	   tt_reset_emalloc();
	   if (tt_timer_pending) {
	      tt_timer_pending = FALSE;
	      tt_do_action(tt_timer_action);
	      }
	   switch (a->op) {
	      case BEEP_OP    : window_bell(tt_base_window->frame);
	   		        break;
	      case BREAK_OP   : break_pending = TRUE;
	   		        break;
	      case CLOSE_OP   : if (in_a_popup)
	      			   close_pending = TRUE;
	      			else
	      			   do_close();
	   		        break;
	      case CONTINUE_OP: continue_pending = TRUE;
	   		        break;
	      case DISPLAY_OP : if (a->expr->symbol->kind == SYMBOL_SYMBOL)
	      			   abend("display: cannot display %s, which is not a dialog box or gadget", a->expr->symbol->name);
	      			else if (a->expr->symbol->kind == SYMBOL_GADGET) {
	      			   if (a->expr->symbol->gadget == NULL)
	      			      abend("dialog box %s was never defined", a->expr->symbol->name);
	      			   panel_set(a->expr->symbol->gadget->panel_item, PANEL_SHOW_ITEM, TRUE, 0);
	      			   }
	      			else {
	      			   if ((d = a->expr->symbol->dialog) == NULL)
	      			      abend("dialog box %s was never defined", a->expr->symbol->name);
	      			   window_set(d->frame, WIN_SHOW, TRUE, 0);
	      			   tt_do_action(d->open_action);
	      			   d->is_open = TRUE;
	      			   d->is_popup = FALSE;
	      			   }
	   		        break;
	      case EXIT_OP    : if (in_a_popup)
	      			   exit_pending = TRUE;
	      			else
	      			   exit(0);
	   		        break;
	      case EXPR_OP    : tt_eval(a->expr);
	   		        break;
	      case FOR_OP     : for (tt_eval(a->init); (int) tt_eval(a->expr)->number; tt_eval(a->term)) {
	      			   tt_do_action(a->body);
	      			   if (break_pending) {
	      			      break_pending = FALSE;
	      			      break;
	      			      }
	      			   if (continue_pending) {
	      			      continue_pending = FALSE;
	      			      continue;
	      			      }
	      			   }
	   		        break;
	      case IF_OP      : tt_do_action(((int) tt_eval(a->expr)->number)? a->body : a->else_part);
	   		        break;
	      case OPEN_OP    : if (in_a_popup)
	      			   open_pending = TRUE;
	      			else
	      			   do_open();
	   		        break;
	      case POPUP_OP   : if (a->expr->symbol->kind != SYMBOL_DIALOG)
	      			   abend("popup: %s is not a dialog box", a->expr->symbol->name);
	      			else if ((d = a->expr->symbol->dialog) == NULL)
	      			   abend("dialog box %s was never defined", a->expr->symbol->name);
	      			else if (d->is_open)
	      			   abend("popup: dialog box %s is already open", a->expr->symbol->name);
	      			else if (in_a_popup)
	      			   abend("nested popup windows are not allowed");
	      			d->is_open = TRUE;
	      			d->is_popup = TRUE;
	      			tt_do_action(d->open_action);
	      			in_a_popup = TRUE;
	      			window_loop(d->frame);
	      			in_a_popup = FALSE;
	      			tt_do_action(d->close_action);
	      			d->is_open = FALSE;
	      			d->is_popup = TRUE;
	      			if (close_pending)
	      			   do_close();
	      			if (open_pending)
	      			   do_open();
	      			if (exit_pending)
	      			   exit(0);
	      			close_pending = open_pending = exit_pending = FALSE;
	   		        break;
	      case REMOVE_OP  : if (a->expr->symbol->kind == SYMBOL_SYMBOL)
	      			   abend("remove: cannot remove %s, which is not a dialog box or gadget", a->expr->symbol->name);
	      			else if (a->expr->symbol->kind == SYMBOL_GADGET) {
	      			   if (a->expr->symbol->gadget == NULL)
	      			      abend("gadget %s was never defined", a->expr->symbol->name);
	      			   panel_set(a->expr->symbol->gadget->panel_item, PANEL_SHOW_ITEM, FALSE, 0);
	      			   }
	      			else {
	      			   if ((d = a->expr->symbol->dialog) == NULL)
	      			      abend("dialog box %s was never defined", a->expr->symbol->name);
	      			   if (d->is_open)
	      			      if (d->is_popup)
	      			         window_return(0);
	      			      else {
	      			         window_set(d->frame, WIN_SHOW, FALSE, 0);
	      			         tt_do_action(d->close_action);
	      			         d->is_open = FALSE;
	      			         d->is_popup = FALSE;
	      			         }
	      			   }
	   		        break;
	      case SEND_OP    : send_text(tt_string_of(tt_eval(a->expr)));
	   		        break;
	      case WHILE_OP   : while ((int) tt_eval(a->expr)->number) {
	      			   tt_do_action(a->body);
	      			   if (break_pending) {
	      			      break_pending = FALSE;
	      			      break;
	      			      }
	      			   if (continue_pending) {
	      			      continue_pending = FALSE;
	      			      continue;
	      			      }
	      			   }
	   		        break;
	      default	      : abend("Internal error! Undefined action: %d", a->op);
	      }
	   }
	if (--tt_action_depth == 0) {
	   if (continue_pending)
	      abend("continue action used outside of a while or for action");
	   break_pending = FALSE;
	   }
}
