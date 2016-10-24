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


#include	<ctype.h>

#include	"tooltool.h"

#include	<suntool/tty.h>

#define		TOOLTOOL_ICON		"tooltool.icon"

PRIVATE	short	icon_bits[] = {
#include	TOOLTOOL_ICON
			      };
mpr_static(tt_default_icon_pr, 64, 64, 1, icon_bits);

EXPORT	Tty	tty = NULL;

PUBLIC	event_proc(),
	notify_proc(),
	background_proc(),
	close_proc(),
	tty_handler(),
	tt_dialog_done();

/************************************************************************/
/* This group of routines deals with laying out the tooltool windows	*/
/************************************************************************/

/************************************************************************/
PRIVATE	gadget_rows(d)

d_ptr	d;

{	int	j, k, extra, count, row, height;
	g_ptr	b, next, start;

	tt_build_images(d);
	for (next = d->gadgets, row = 4, count = 0; next; row += height + 4) {
	   extra = (int) window_get(d->panel, WIN_WIDTH) - 4;
	   for (b = start = next, height = 0; b; b = b->next)
	      if (b->width + 4 > extra) { /* no room for this gadget */
	         next = b;
	         break;
	         }
	      else {
	         extra -= b->width + 4;
	         count++;
	         if (b->height > height)
	            height = b->height;
	         }
	   if (b == NULL)
	      next = NULL;
	   if (next == start) {
	      next = start->next;
	      height = start->height;
	      count++;
	      }
	   if (!d->justified)
	      extra = 0;
	   for (b = start, j = 4, count--; b != next; b = b->next) {
	      if (d->g_align == ALIGN_TOP)
	         k = row;
	      else if (d->g_align == ALIGN_MIDDLE)
	         k = row + (height - b->height) / 2;
	      else
	         k = row + height - b->height;
	      tt_make_gadget(d, b, j, k);
	      if (count > 0) {
	         j += b->width + 4 + (extra / count);
	         extra -= extra / count--;
	         }
	      }
	   }
	panel_fit_height(d->panel);
}

/************************************************************************/
PRIVATE	gadget_columns(d)

d_ptr	d;

{	int	j, k, extra, count, col, width;
	g_ptr	b, next, start;

	tt_build_images(d);
	for (next = d->gadgets, col = count = 0; next; col += width + 4) {
	   extra = (int) window_get(d->panel, WIN_HEIGHT) - 4;
	   for (b = start = next, width = 0; b; b = b->next)
	      if (b->height + 4 > extra) { /* no room for this gadget */
	         next = b;
	         break;
	         }
	      else {
	         extra -= b->height + 4;
	         count++;
	         if (b->width > width)
	            width = b->width;
	         }
	   if (b == NULL)
	      next = NULL;
	   if (next == start) {
	      next = start->next;
	      width = start->width;
	      count++;
	      }
	   if (!d->justified)
	      extra = 0;
	   for (b = start, j = 4, count--; b != next; b = b->next) {
	      if (d->g_align == ALIGN_TOP)
	         k = 4 + col;
	      else if (d->g_align == ALIGN_MIDDLE)
	         k = 4 + col + (width - b->width) / 2;
	      else
	         k = 4 + col + width - b->width;
	      tt_make_gadget(d, b, k, j);
	      if (count > 0) {
	         j += b->height + 4 + (extra / count);
	         extra -= extra / count--;
	         }
	      }
	   }
	panel_fit_width(d->panel);
}

/************************************************************************/
EXPORT	build_window(argc, argv)

int	argc;
char	**argv;

{	int	i, j, w, h;
	g_ptr	b, start, next;
	char	*args[64];
	struct	pixrect	*icon_pr;
	Icon	ic;
	Rect	*fr, *sr;
	d_ptr	d;
	static	char	*pos_hack[5];

	if (tt_icon != NULL)
	   icon_pr = tt_load_icon(tt_icon);
	else
	   icon_pr = &tt_default_icon_pr;
	ic = icon_create(ICON_IMAGE, icon_pr,
			 ICON_LABEL, "",
			 ICON_WIDTH, icon_pr->pr_size.x,
			 ICON_HEIGHT, icon_pr->pr_size.y,
			 0);
	tt_base_window->frame = window_create(NULL, FRAME,
				 FRAME_ARGC_PTR_ARGV, &argc, argv,
				 FRAME_ICON, ic,
				 WIN_CLIENT_DATA, tt_base_window,
			      0);
	if (tt_base_window->label)
	   window_set(tt_base_window->frame, FRAME_LABEL, tt_base_window->label, 0);
	if (tt_base_window->win_x != -1)
	   window_set(tt_base_window->frame, WIN_X, tt_base_window->win_x, WIN_Y, tt_base_window->win_y, 0);

	args[0] = tt_program;
	args[1] = POLLING_MAGIC_NUMBER;
	args[2] = safe_malloc(10);
	args[3] = safe_malloc(10);
	sprintf(args[2], "%d", tt_base_window->columns / (tt_base_window->is_chars? 1 : charwidth_of(tt_a_font)));
	sprintf(args[3], "%d", tt_base_window->rows / (tt_base_window->is_chars? 1 : charheight_of(tt_a_font)));
	tokenize(tt_application, &i, args + 4, 60);
	for (j = 1, i += 4; j < argc; j++)
	   args[i++] = argv[j];
	args[i] = NULL;
	if (tt_base_window->gadgets == NULL) {
	   if (*tt_application)
	      tty = window_create(tt_base_window->frame, TTY,
				     tt_base_window->is_chars? WIN_ROWS : WIN_HEIGHT, tt_base_window->rows,
				     tt_base_window->is_chars? WIN_COLUMNS : WIN_WIDTH, tt_base_window->columns,
				     WIN_FONT, tt_a_font,
				     TTY_QUIT_ON_CHILD_DEATH, TRUE,
				     TTY_ARGV, args,
			          0);
	   }
	else if (tt_base_window->gadget_pos == G_TOP) {
	   tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
	   			    WIN_ROWS, 24,
	   			    WIN_WIDTH, tt_base_window->is_chars? charwidth_of(tt_a_font) * tt_base_window->columns : tt_base_window->columns,
	   			    WIN_FONT, tt_base_window->g_font,
				    WIN_CLIENT_DATA, tt_base_window,
	   			    PANEL_ACCEPT_KEYSTROKE, !tt_base_window->text_items_exist,
	   			    PANEL_BACKGROUND_PROC, background_proc,
	   			    PANEL_NOTIFY_PROC, notify_proc,
	   			    PANEL_EVENT_PROC, event_proc,
	   			 0);
	   gadget_rows(tt_base_window);
	   if (*tt_application)
	      tty = window_create(tt_base_window->frame, TTY,
				     tt_base_window->is_chars? WIN_ROWS : WIN_HEIGHT, tt_base_window->rows,
				     tt_base_window->is_chars? WIN_COLUMNS : WIN_WIDTH, tt_base_window->columns,
				     WIN_BELOW, tt_base_window->panel,
				     WIN_X, 0,
				     WIN_FONT, tt_a_font,
				     TTY_QUIT_ON_CHILD_DEATH, TRUE,
				     TTY_ARGV, args,
			          0);
	   }
	else if (tt_base_window->gadget_pos == G_BOTTOM) {
	   if (*tt_application)
	      tty = window_create(tt_base_window->frame, TTY,
				     tt_base_window->is_chars? WIN_ROWS : WIN_HEIGHT, tt_base_window->rows,
				     tt_base_window->is_chars? WIN_COLUMNS : WIN_WIDTH, tt_base_window->columns,
				     WIN_FONT, tt_a_font,
				     TTY_QUIT_ON_CHILD_DEATH, TRUE,
				     TTY_ARGV, args,
			          0);
	   if (tty && tt_base_window->rows > 0 && tt_base_window->columns > 0)
	      tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
	   			       		       WIN_BELOW, tty,
	   			       		       WIN_X, 0,
	   			       		    0);
	   else
	      tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
	   			       		       WIN_X, 0,
	   			       		       WIN_Y, 0,
	   			       		    0);
	   window_set(tt_base_window->panel,
	   		 WIN_ROWS, 24,
	   		 WIN_WIDTH, tt_base_window->is_chars? charwidth_of(tt_a_font) * tt_base_window->columns : tt_base_window->columns,
	   		 WIN_FONT, tt_base_window->g_font,
			 WIN_CLIENT_DATA, tt_base_window,
	   		 PANEL_ACCEPT_KEYSTROKE, !tt_base_window->text_items_exist,
	   		 PANEL_BACKGROUND_PROC, background_proc,
	   		 PANEL_NOTIFY_PROC, notify_proc,
	   		 PANEL_EVENT_PROC, event_proc,
	   	      0);
	   gadget_rows(tt_base_window);
	   }
	else if (tt_base_window->gadget_pos == G_LEFT)  {
	   tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
	   			    WIN_HEIGHT, tt_base_window->is_chars? charheight_of(tt_a_font) * tt_base_window->rows : tt_base_window->rows,
	   			    WIN_COLUMNS, 80,
	   			    WIN_FONT, tt_base_window->g_font,
				    WIN_CLIENT_DATA, tt_base_window,
	   			    PANEL_ACCEPT_KEYSTROKE, !tt_base_window->text_items_exist,
	   			    PANEL_BACKGROUND_PROC, background_proc,
	   			    PANEL_NOTIFY_PROC, notify_proc,
	   			    PANEL_EVENT_PROC, event_proc,
	   			 0);
	   gadget_columns(tt_base_window);
	   if (*tt_application)
	      tty = window_create(tt_base_window->frame, TTY,
				     tt_base_window->is_chars? WIN_ROWS : WIN_HEIGHT, tt_base_window->rows,
				     tt_base_window->is_chars? WIN_COLUMNS : WIN_WIDTH, tt_base_window->columns,
				     WIN_RIGHT_OF, tt_base_window->panel,
				     WIN_Y, 0,
				     WIN_FONT, tt_a_font,
				     TTY_QUIT_ON_CHILD_DEATH, TRUE,
				     TTY_ARGV, args,
			          0);
	   }
	else if (tt_base_window->gadget_pos == G_RIGHT) {
	   if (*tt_application)
	      tty = window_create(tt_base_window->frame, TTY,
				     tt_base_window->is_chars? WIN_ROWS : WIN_HEIGHT, tt_base_window->rows,
				     tt_base_window->is_chars? WIN_COLUMNS : WIN_WIDTH, tt_base_window->columns,
				     WIN_FONT, tt_a_font,
				     TTY_QUIT_ON_CHILD_DEATH, TRUE,
				     TTY_ARGV, args,
			          0);
	   if (tty && tt_base_window->rows > 0 && tt_base_window->columns > 0)
	      tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
				    		       WIN_RIGHT_OF, tty,
				    		       WIN_Y, 0,
				    		    0);
	   else
	      tt_base_window->panel = window_create(tt_base_window->frame, PANEL,
				    		       WIN_X, 0,
				    		       WIN_Y, 0,
				    		    0);
	   window_set(tt_base_window->panel,
	   	         WIN_HEIGHT, tt_base_window->is_chars? charheight_of(tt_a_font) * tt_base_window->rows : tt_base_window->rows,
	   	         WIN_COLUMNS, 80,
	   	         WIN_FONT, tt_base_window->g_font,
		         WIN_CLIENT_DATA, tt_base_window,
	   	         PANEL_ACCEPT_KEYSTROKE, !tt_base_window->text_items_exist,
	   	         PANEL_BACKGROUND_PROC, background_proc,
	   	         PANEL_NOTIFY_PROC, notify_proc,
	   	         PANEL_EVENT_PROC, event_proc,
	   	      0);
	   gadget_columns(tt_base_window);
	   }
	window_fit(tt_base_window->frame);

	fr = (Rect *) window_get(tt_base_window->frame, FRAME_OPEN_RECT);
	sr = (Rect *) window_get(tt_base_window->frame, WIN_SCREEN_RECT);
	if (fr->r_left + fr->r_width > sr->r_width)
	   window_set(tt_base_window->frame, WIN_X, max(sr->r_width - fr->r_width, 0), 0);
	if (fr->r_top + fr->r_height > sr->r_height)
	   window_set(tt_base_window->frame, WIN_Y, max(sr->r_height - fr->r_height, 0), 0);

	fr = (Rect *) window_get(tt_base_window->frame, FRAME_CLOSED_RECT);
	for (d = tt_base_window->next; d; d = d->next) {
	   if (d->g_align == NO_ALIGN)
	      d->g_align = ALIGN_TOP;
	   pos_hack[0] = "";
	   pos_hack[1] = "-WP";
	   pos_hack[2] = safe_malloc(7);
	   pos_hack[3] = safe_malloc(7);
	   pos_hack[4] = NULL;
	   sprintf(pos_hack[2], "%d", fr->r_left);
	   sprintf(pos_hack[3], "%d", fr->r_top);
	   d->frame = window_create(tt_base_window->frame, FRAME,
	   			       FRAME_SHOW_LABEL, FALSE,
	   			       FRAME_DONE_PROC, tt_dialog_done,
	   			       FRAME_ARGS, 4, pos_hack,
	   			       WIN_CLIENT_DATA, d,
	   			    0);
	   if (d->label)
	      window_set(d->frame, FRAME_LABEL, d->label, FRAME_SHOW_LABEL, TRUE, 0);
	   d->panel = window_create(d->frame, PANEL,
	   			       WIN_HEIGHT, d->is_chars? charwidth_of(d->g_font) * d->rows : d->rows,
	   			       WIN_WIDTH, d->is_chars? charwidth_of(d->g_font) * d->columns : d->columns,
	   			       WIN_FONT, d->g_font,
	   			       WIN_CLIENT_DATA, d,
	   			       PANEL_ACCEPT_KEYSTROKE, !d->text_items_exist,
	   			       PANEL_BACKGROUND_PROC, background_proc,
	   			       PANEL_NOTIFY_PROC, notify_proc,
	   			       PANEL_EVENT_PROC, event_proc,
	   			    0);
	   if (d->gadget_pos == G_TOP || d->gadget_pos == G_BOTTOM)
	      gadget_rows(d);
	   else
	      gadget_columns(d);
	   window_fit(d->panel);
	   window_fit(d->frame);
	   }

	notify_interpose_event_func(tt_base_window->frame, close_proc, NOTIFY_SAFE);
	if (tt_base_window->panel)
	   notify_interpose_event_func(tt_base_window->panel, close_proc, NOTIFY_SAFE);

	if (tty) {
	   notify_interpose_event_func(tty, tty_handler, NOTIFY_SAFE);
	   tt_ttymenu = (Menu) window_get(tty, WIN_MENU);
	   }

	if (tty == NULL || tt_base_window->rows <= 0 || tt_base_window->columns <= 0) {
	   if (tty)
	      window_set(tty, WIN_SHOW, FALSE, 0);
	   if (tt_base_window->panel)
	      window_fit(tt_base_window->panel);
	   window_fit(tt_base_window->frame);
	   }

	fr = (Rect *) window_get(tt_base_window->frame, FRAME_OPEN_RECT);
	window_set(tt_base_window->frame, WIN_X, 0, WIN_Y, 0, 0);
	for (d = tt_base_window->next; d; d = d->next)
	   if (d->win_x != -1) {
	      window_set(d->frame, WIN_X, d->win_x, WIN_Y, d->win_y, 0);
	      w = (int) window_get(d->frame, WIN_WIDTH);
	      h = (int) window_get(d->frame, WIN_HEIGHT);
	      if (d->win_x + w > sr->r_width)
	         window_set(d->frame, WIN_X, max(sr->r_width - w, 0), 0);
	      if (d->win_y + h > sr->r_height)
	         window_set(d->frame, WIN_Y, max(sr->r_height - h, 0), 0);
	      }
	   else
	      window_set(d->frame,
	      		 WIN_X, (sr->r_width - (int) window_get(d->frame, WIN_WIDTH)) / 2,
	      		 WIN_Y, (sr->r_height - (int) window_get(d->frame, WIN_HEIGHT)) / 2,
	      		 0);
	window_set(tt_base_window->frame, WIN_X, fr->r_left, WIN_Y, fr->r_top, 0);

	init_function_fix(tt_base_window->frame);
	if (tty)
	   init_function_fix(tty);
	if (tt_base_window->panel)
	   init_function_fix(tt_base_window->panel);
	for (d = tt_base_window->next; d; d = d->next) {
	   init_function_fix(d->frame);
	   init_function_fix(d->panel);
	   }

	tt_do_action(tt_initial_action);
}
