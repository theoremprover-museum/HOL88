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
#include	<math.h>

#include	"tooltool.h"

/************************************************************************/
PRIVATE	v_ptr	do_compare(op, l, r)

register	int	op;
register	v_ptr	l;
register	v_ptr	r;

{	register	char	*p, *q;

	if (is_number(l) && is_number(r))
	   switch (op) {
	      case E_EQUAL         : return(tt_int_result(l->number == r->number));
	      case E_GREATER       : return(tt_int_result(l->number > r->number));
	      case E_GREATER_EQUAL : return(tt_int_result(l->number >= r->number));
	      case E_LESS          : return(tt_int_result(l->number < r->number));
	      case E_LESS_EQUAL    : return(tt_int_result(l->number <= r->number));
	      case E_NOT_EQUAL     : return(tt_int_result(l->number != r->number));
	      }
	else {
	   p = tt_string_of(l);
	   q = tt_string_of(r);
	   switch (op) {
	      case E_EQUAL         : return(tt_int_result(strcmp(p, q) == 0));
	      case E_GREATER       : return(tt_int_result(strcmp(p, q) > 0));
	      case E_GREATER_EQUAL : return(tt_int_result(strcmp(p, q) >= 0));
	      case E_LESS          : return(tt_int_result(strcmp(p, q) < 0));
	      case E_LESS_EQUAL    : return(tt_int_result(strcmp(p, q) <= 0));
	      case E_NOT_EQUAL     : return(tt_int_result(strcmp(p, q) != 0));
	      }
	   }
}

/************************************************************************/
PRIVATE	v_ptr	do_array_ref(a, i)

register	v_ptr	a;
register	v_ptr	i;

{	register	v_ptr	v;
	register	char	*s;
	register	int	cmp;

	s = tt_string_of(i);
	if (is_array(a)) {
	   for (v = a->value; v; )
	      if ((cmp = tt_dict_compare(s, v->index)) == 0)
	         break;
	      else if (cmp < 0)
	         v = v->left;
	      else
	         v = v->right;
	   if (v)
	      return(v);
	   }
	else {
	   a->kind = V_ARRAY;
	   a->value = NULL;
	   }
	v = (v_ptr) safe_malloc(sizeof(v_data));
	v->kind = V_NOTHING;
	v->number = 0.0;
	v->str = "";
	v->value = NULL;
	v->left = NULL;
	v->right = NULL;
	tt_insert_array(&(a->value), strsave(s), v);
	return(v);
}

/************************************************************************/
PRIVATE	v_ptr	dup_array(v)

register	v_ptr	v;

{	register	v_ptr	new;

	if (v == NULL)
	   return(NULL);
	new = (v_ptr) safe_malloc(sizeof(v_data));
	new->kind = v->kind;
	new->number = v->number;
	new->left = dup_array(v->left);
	new->right = dup_array(v->right);
	new->index = strsave(v->index);
	if (is_array(new))
	   new->value = dup_array(v->value);
	else
	   new->str = is_number(new)? NULL : strsave(v->str);
	return(new);
}

/************************************************************************/
PRIVATE	char	*concatenate(v, separator)

register	v_ptr	v;
char		separator;

{	register	char	*l, *m, *r, *p;
	char	buf[2];

	if (v == NULL)
	   return("");
	buf[0] = separator;
	buf[1] = '\0';
	l = concatenate(v->left, separator);
	m = tt_string_of(v);
	r = concatenate(v->right, separator);
	p = tt_emalloc(strlen(l) + strlen(m) + strlen(r) + 3);
	strcpy(p, l);
	if (*m) {
	   if (*p)
	      strcat(p, buf);
	   strcat(p, m);
	   }
	if (*r) {
	   if (*p)
	      strcat(p, buf);
	   strcat(p, r);
	   }
	return(p);
}

/************************************************************************/
PRIVATE	free_array(v)

v_ptr	v;

{
	if (v) {
	   if (is_array(v))
	      safe_free(v->value);
	   safe_free(v->index);
	   free_array(v->left);
	   free_array(v->right);
	   safe_free(v);
	   }
}

/************************************************************************/
PRIVATE	do_assign(l, r)

register	v_ptr	l;
register	v_ptr	r;

{
	if (is_array(l))
	   free_array(l->value);
	l->kind = (r->kind & V_TYPES) | (l->kind & V_SPECIAL);
	if (is_gadget(l))
	   switch (l->gadget->kind) {
	      case GADGET_CHOICE :
	      case GADGET_SLIDER : panel_set(l->gadget->panel_item, PANEL_VALUE, (int) r->number, 0);
	      			   break;
	      case GADGET_TEXT   : panel_set(l->gadget->panel_item, PANEL_VALUE, tt_string_of(r), 0);
	      			   break;
/*	      case GADGET_LABEL  : panel_set(l->gadget->panel_item, PANEL_LABEL_STRING, tt_string_of(r), 0);
	      			   break;*/
	      default		 : abend("cannot assign a value to a button or menu");
	      }
	if (is_array(l))
	   l->value = dup_array(r->value);
	else if (is_number(l))
	   l->number = r->number;
	else {
	   l->str = strsave(r->str);
	   l->number = r->number;
	   }
	if (is_interval(l))
	   tt_set_timer((int) l->number, ((int) (l->number * 1000000.0)) % 1000000);
}

/************************************************************************/
EXPORT	v_ptr	tt_int_result(i)

int	i;

{	char	buf[20];
	register	v_ptr	v;

	v = (v_ptr) tt_emalloc(sizeof(v_data));
	v->str = NULL;
	v->kind = V_NUMBER;
	v->number = i;
	v->left = NULL;
	v->right = NULL;
	return(v);
}

/************************************************************************/
EXPORT	v_ptr	tt_double_result(r)

double	r;

{	char	buf[20];
	register	v_ptr	v;

	v = (v_ptr) tt_emalloc(sizeof(v_data));
	v->str = NULL;
	v->kind = V_NUMBER;
	v->number = r;
	v->left = NULL;
	v->right = NULL;
	return(v);
}

/************************************************************************/
EXPORT	v_ptr	tt_string_result(s)

char	*s;

{	char	buf[20];
	double	atof();
	register	v_ptr	v;

	v = (v_ptr) tt_emalloc(sizeof(v_data));
	if (tt_is_temp(s))
	   v->str = s;
	else
	   v->str = estrsave(s);
	v->kind = V_NOTHING;
	v->number = tt_is_number(s)? atof(s) : 0.0;
	v->left = NULL;
	v->right = NULL;
	return(v);
}

/************************************************************************/
EXPORT	char	*tt_string_of(v)

register	v_ptr	v;

{	register	char	*p;
	char	buf[20], *delimiters;

	if (is_array(v)) {
	   if (is_array(tt_delimiters->value) || (delimiters = tt_string_of(tt_delimiters->value)) == NULL)
	      delimiters = " ";
	   return(concatenate(v->value, *delimiters));
	   }
	else if (is_number(v)) {
	   sprintf(buf, "%1.12g", v->number);
	   return(estrsave(buf));
	   }
	else
	   return(v->str);
}

/************************************************************************/
EXPORT	v_ptr	tt_insert_array(array, index, value)

register	v_ptr	*array;
register	char	*index;
register	v_ptr	value;

{	int	cmp;

	while (*array)
	   if ((cmp = tt_dict_compare(index, (*array)->index)) == 0)
	      abend("%s should not exist in array", index);
	   else if (cmp < 0)
	      array = &((*array)->left);
	   else
	      array = &((*array)->right);
	*array = value;
	value->index = index;
}

/************************************************************************/
EXPORT	e_ptr	tt_make_expr(op, arg1, arg2, arg3)

int	op;
e_ptr	arg1, arg2, arg3;

{	e_ptr	e;

	e = (e_ptr) safe_malloc(sizeof(e_data));
	switch (e->op = op) {
	   case E_QUESTION      : 
	   			  e->extra = arg3;
	   case E_AND           :
	   case E_ARRAY_REF     :
	   case E_ASSIGN_AND    :
	   case E_ASSIGN_DIVIDE :
	   case E_ASSIGN_MINUS  :
	   case E_ASSIGN_MODULO :
	   case E_ASSIGN_OR     :
	   case E_ASSIGN_PLUS   :
	   case E_ASSIGN_TIMES  :
	   case E_ASSIGN_XOR    :
	   case E_ASSIGNMENT    :
	   case E_COMMA         :
	   case E_DIVIDE        :
	   case E_EQUAL         :
	   case E_GREATER       :
	   case E_GREATER_EQUAL :
	   case E_LEFT_SHIFT    :
	   case E_LESS          :
	   case E_LESS_EQUAL    :
	   case E_LOGICAL_AND   :
	   case E_LOGICAL_NOT   :
	   case E_LOGICAL_OR    :
	   case E_MINUS         :
	   case E_MODULO        :
	   case E_NOT_EQUAL     :
	   case E_OR            :
	   case E_PLUS          :
	   case E_RIGHT_SHIFT   :
	   case E_TIMES         :
	   case E_XOR           : 
	   			  e->right = arg2;
	   case E_COMPLEMENT    :
	   case E_PAREN         :
	   case E_POSTDECREMENT :
	   case E_POSTINCREMENT :
	   case E_PREDECREMENT  :
	   case E_PREINCREMENT  :
	   case E_UMINUS        :
	   			  e->left = arg1;
	   			  break;
	   case E_FUNC_ID       : e->func = (f_ptr) arg1;
	   			  e->left = arg2;
	   			  break;
	   case E_STRING        : e->string = (char *) arg1;
	   			  break;
	   case E_NUMBER	: e->value = *((double *) arg1);
	   			  break;
	   case E_SYMBOL        : e->symbol = (s_ptr) arg1;
	   			  break;
	   }
	return(e);
}

/************************************************************************/
EXPORT	v_ptr	tt_eval(e)

register	e_ptr	e;

{	double	r;
	int	i;
	v_ptr	v, w;
	char	*p, *q, *s;

	if (e == NULL)
	   return(NULL);
	switch (e->op) {
	   case E_AND           : return(tt_int_result(((int) tt_eval(e->left)->number) & ((int) tt_eval(e->right)->number)));
	   case E_ARRAY_REF     : return(do_array_ref(tt_eval(e->left), tt_eval(e->right)));
	   case E_ASSIGN_AND    : v = tt_eval(e->left);
	   			  do_assign(v, tt_int_result(((int) v->number) & ((int) tt_eval(e->right)->number)));
	   			  return(v);
	   case E_ASSIGN_DIVIDE : v = tt_eval(e->left);
	   			  if ((r = tt_eval(e->right)->number) == 0.0)
	   			     abend("division by zero");
	   			  else {
	   			     do_assign(v, tt_double_result(v->number / r));
	   			     return(v);
	   			     }
	   case E_ASSIGN_MINUS  : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result(v->number - tt_eval(e->right)->number));
	   			  return(v);
	   case E_ASSIGN_MODULO : v = tt_eval(e->left);
	   			  do_assign(v, tt_int_result(((int) v->number) % ((int) tt_eval(e->right)->number)));
	   			  return(v);
	   case E_ASSIGN_OR     : v = tt_eval(e->left);
	   			  do_assign(v, tt_int_result(((int) v->number) | ((int) tt_eval(e->right)->number)));
	   			  return(v);
	   case E_ASSIGN_PLUS   : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result(v->number + tt_eval(e->right)->number));
	   			  return(v);
	   case E_ASSIGN_TIMES  : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result(v->number * tt_eval(e->right)->number));
	   			  return(v);
	   case E_ASSIGN_XOR    : v = tt_eval(e->left);
	   			  do_assign(v, tt_int_result(((int) v->number) ^ ((int) tt_eval(e->right)->number)));
	   			  return(v);
	   case E_ASSIGNMENT    : do_assign(tt_eval(e->left), v = tt_eval(e->right));
	   			  return(v);
	   case E_COMMA         : p = tt_string_of(tt_eval(e->left));
	   			  q = tt_string_of(tt_eval(e->right));
	   			  s = tt_emalloc(strlen(p) + strlen(q) + 1);
	   			  strcpy(s, p);
	   			  strcat(s, q);
	   			  return(tt_string_result(s));
	   case E_COMPLEMENT    : return(tt_int_result(~((int) tt_eval(e->left)->number)));
	   case E_DIVIDE        : if ((r = tt_eval(e->right)->number) == 0.0)
	   			     abend("division by zero");
	   			  else
	   			     return(tt_double_result(tt_eval(e->left)->number / r));
	   case E_EQUAL         :
	   case E_GREATER       :
	   case E_GREATER_EQUAL :
	   case E_LESS          :
	   case E_LESS_EQUAL    :
	   case E_NOT_EQUAL     : return(do_compare(e->op, tt_eval(e->left), tt_eval(e->right)));
	   case E_FUNC_ID       : return(e->func(e->left));
	   case E_LEFT_SHIFT    : return(tt_int_result(((int) tt_eval(e->left)->number) << ((int) tt_eval(e->right)->number)));
	   case E_LOGICAL_AND   : return(tt_int_result(((int) tt_eval(e->left)->number) && ((int) tt_eval(e->right)->number)));
	   case E_LOGICAL_NOT   : return(tt_int_result(!((int) tt_eval(e->left)->number)));
	   case E_LOGICAL_OR    : return(tt_int_result(((int) tt_eval(e->left)->number) || ((int) tt_eval(e->right)->number)));
	   case E_MINUS         : return(tt_double_result(tt_eval(e->left)->number - tt_eval(e->right)->number));
	   case E_MODULO        : if ((i = ((int) tt_eval(e->right)->number)) == 0)
	   			     abend("modulus by zero");
	   			  else
	   			     return(tt_int_result(((int) tt_eval(e->left)->number) % i));
	   case E_NUMBER	: return(tt_double_result(e->value));
	   case E_OR            : return(tt_int_result(((int) tt_eval(e->left)->number) | ((int) tt_eval(e->right)->number)));
	   case E_PAREN         : return(tt_eval(e->left));
	   case E_PLUS          : return(tt_double_result(tt_eval(e->left)->number + tt_eval(e->right)->number));
	   case E_POSTDECREMENT : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result((r = v->number) - 1.0));
	   			  return(tt_double_result(r));
	   case E_POSTINCREMENT : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result((r = v->number) + 1.0));
	   			  return(tt_double_result(r));
	   case E_PREDECREMENT  : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result(v->number - 1.0));
	   			  return(v);
	   case E_PREINCREMENT  : v = tt_eval(e->left);
	   			  do_assign(v, tt_double_result(v->number + 1.0));
	   			  return(v);
	   case E_QUESTION      : return(((int) tt_eval(e->left)->number)? tt_eval(e->right) : tt_eval(e->extra));
	   case E_RIGHT_SHIFT   : return(tt_int_result(((int) tt_eval(e->left)->number) >> ((int) tt_eval(e->right)->number)));
	   case E_STRING        : return(tt_string_result(e->string));
	   case E_SYMBOL        : return(tt_get_value(e->symbol));
	   case E_TIMES         : return(tt_double_result(tt_eval(e->left)->number * tt_eval(e->right)->number));
	   case E_UMINUS        : return(tt_double_result(-tt_eval(e->left)->number));
	   case E_XOR           : return(tt_int_result(((int) tt_eval(e->left)->number) ^ ((int) tt_eval(e->right)->number)));
	   }
}
