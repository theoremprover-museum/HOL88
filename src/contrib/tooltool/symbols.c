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
#include	<sys/types.h>
#include	<sys/dir.h>
#include	<pwd.h>

#include	<suntool/sunview.h>
#include	<suntool/icon_load.h>

#include	"tooltool.h"

PRIVATE	s_ptr	symbols = NULL;

/************************************************************************/
PRIVATE	s_ptr	create_symbol(name, sp)

char	*name;
s_ptr	*sp;

{
	while (*sp)
	   if (strcmp(name, (*sp)->name) < 0)
	      sp = &((*sp)->left);
	   else
	      sp = &((*sp)->right);
	*sp = (s_ptr) safe_malloc(sizeof(s_data));
	(*sp)->name = strsave(name);
	(*sp)->kind = SYMBOL_SYMBOL;
	(*sp)->gadget = NULL;
	(*sp)->dialog = NULL;
	(*sp)->left = NULL;
	(*sp)->right = NULL;
	(*sp)->value = (v_ptr) safe_malloc(sizeof(v_data));
	(*sp)->value->kind = V_NOTHING;
	(*sp)->value->number = 0.0;
	(*sp)->value->str = "";
	(*sp)->value->value = NULL;
	(*sp)->value->left = NULL;
	(*sp)->value->right = NULL;
	(*sp)->value->index = NULL;
	return(*sp);
}
	
/************************************************************************/
EXPORT	s_ptr	tt_find_symbol(name)

char	*name;

{	s_ptr	s;
	int	i;

	for (s = symbols; s; )
	   if ((i = strcmp(name, s->name)) == 0)
	      break;
	   else if (i < 0)
	      s = s->left;
	   else
	      s = s->right;
	if (s == NULL)
	   s = create_symbol(name, &symbols);
	return(s);
}

/************************************************************************/
EXPORT	v_ptr	tt_get_value(s)

s_ptr	s;

{	v_ptr	v;
	static	char	buf[20];

	if (s == NULL)
	   return(NULL);
	else if (s->kind == SYMBOL_SYMBOL)
	   return(s->value);
	else if (s->kind == SYMBOL_DIALOG)
	   abend("attempted to get value of dialog box %s", s->name);
	else {
	   switch (s->gadget->kind) {
	      case GADGET_TEXT   : v = tt_string_result(panel_get(s->gadget->panel_item, PANEL_VALUE));
	   			   break;
	      case GADGET_CHOICE : 
	      case GADGET_SLIDER : v = tt_int_result(panel_get(s->gadget->panel_item, PANEL_VALUE));
	   			   break;
/*	      case GADGET_LABEL  : v = tt_string_result(panel_get(s->gadget->panel_item, PANEL_LABEL_STRING));
	      			   break;*/
	      default		 : v = tt_int_result(0);
	      }
	   v->kind |= V_GADGET;
	   v->gadget = s->gadget;
	   return(v);
	   }
}

/************************************************************************/
EXPORT	tt_make_intrinsic_symbols()

{	s_ptr	interval;

	tt_mouse_x = tt_find_symbol("mouse_x");
	tt_mouse_y = tt_find_symbol("mouse_y");
	interval = tt_find_symbol("interval");
	interval->value->kind |= V_INTERVAL;
	tt_delimiters = tt_find_symbol("delimiters");
	tt_delimiters->value->kind = 0;
	tt_delimiters->value->str = " \t\n\r\"'";
}
