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
#include	<pwd.h>
#include	<grp.h>

#include	<sys/types.h>
#include	<sys/stat.h>
#include	<sys/file.h>

#include	"tooltool.h"

PUBLIC	char	*getenv(), *rindex();

PRIVATE	v_ptr	do_cardinality(),
		do_cd(),
		do_executable(),
		do_exists(),
		do_format(),
		do_getenv(),
		do_group(),
		do_head(),
		do_index(),
		do_is_open(),
		do_length(),
		do_output_of(),
		do_pwd(),
		do_readable(),
		do_root(),
		do_selection(),
		do_stat(),
		do_substr(),
		do_suffix(),
		do_system(),
		do_tail(),
		do_tokenize(),
		do_user(),
		do_verify(),
		do_writable();

PRIVATE	struct	{char	*name;
		 f_ptr	func;
		} func[] = {{"cardinality", do_cardinality},
			    {"cd",          do_cd},
			    {"executable",  do_executable},
			    {"exists",      do_exists},
			    {"format",      do_format},
			    {"getenv",      do_getenv},
			    {"group",       do_group},
			    {"head",        do_head},
			    {"index",       do_index},
			    {"is_open",     do_is_open},
			    {"length",      do_length},
			    {"output_of",   do_output_of},
			    {"pwd",         do_pwd},
			    {"readable",    do_readable},
			    {"root",        do_root},
			    {"selection",   do_selection},
			    {"stat",        do_stat},
			    {"substr",      do_substr},
			    {"suffix",      do_suffix},
			    {"system",      do_system},
			    {"tail",        do_tail},
			    {"tokenize",    do_tokenize},
			    {"user",        do_user},
			    {"verify",      do_verify},
			    {"writable",    do_writable},
			    {NULL,          NULL}};

/************************************************************************/
EXPORT	f_ptr	tt_is_function(s)

char	*s;

{	int	i;

	for (i = 0; func[i].name; i++)
	   if (strcmp(func[i].name, s) == 0)
	      return(func[i].func);
	return(NULL);
}

/************************************************************************/
PRIVATE	char	*fix_ctime(time)

int	*time;

{	char	*p;

	p = ctime(time);
	p[24] = '\0';
	return(p);
}

/************************************************************************/
PRIVATE	e_ptr	get_parm(e, n)

e_ptr	e;
int	n;

{	e_ptr	e1;
	int	i, depth;

	if (e == NULL)
	   return(NULL);
	for (e1 = e, depth = 1; e1->op == E_COMMA; e1 = e1->left)
	   depth++;
	if (n > depth)
	   return(NULL);
	else if (depth == 1)
	   return(e);
	else {
	   for (i = depth - n; i; i--)
	      e = e->left;
	   return((n == 1)? e : e->right);
	   }
}

/************************************************************************/
PRIVATE	int	child_count(v)

v_ptr	v;

{
	return(v? child_count(v->left) + child_count(v->right) + 1 : 0);
}

/************************************************************************/
PRIVATE	v_ptr	do_cardinality(e)

e_ptr	e;

{	v_ptr	v;

	v = tt_eval(e);
	if (is_array(v))
	   return(tt_int_result(child_count(v->value)));
	else
	   return(tt_int_result(0));
}

/************************************************************************/
PRIVATE	v_ptr	do_cd(e)

e_ptr	e;

{
	return(tt_int_result(chdir(tt_string_of(tt_eval(e)))? 0 : 1));
}

/************************************************************************/
PRIVATE	v_ptr	do_executable(e)

e_ptr	e;

{	struct	stat	buf;
	int	result;
	char	*p;

	if (stat(p = tt_string_of(tt_eval(e)), &buf) == 0 && access(p, X_OK) == 0)
	   result = 1;
	else
	   result = 0;
	return(tt_int_result(result));
}

/************************************************************************/
PRIVATE	v_ptr	do_exists(e)

e_ptr	e;

{	struct	stat	buf;

	return(tt_int_result((stat(tt_string_of(tt_eval(e)), &buf) == -1)? 0 : 1));
}

/************************************************************************/
PRIVATE	v_ptr	do_format(e)

e_ptr	e;

{	char	fmt[1024], result[1024], *p, *q, *r, *format;
	int	parm;
	e_ptr	e1;

	format = tt_string_of(tt_eval(get_parm(e, 1)));
	for (parm = 1, q = result, p = fmt; *format; format++) {
	   *p++ = *format;
	   if (*format == '%') {
	      for (format++; index("0123456789.-+ #", *format); )
	         *p++ = *format++;
	      *p++ = *format;
	      *p = '\0';
	      if (index("eEfgG", *format)) { /* print as a double */
	         if ((e1 = get_parm(e, ++parm)) == NULL)
	            abend("too few parameters supplied to 'format'");
	         sprintf(q, fmt, tt_eval(e1)->number);
	         }
	      else if (index("cdloxXu", *format)) { /* print as integer */
	         if ((e1 = get_parm(e, ++parm)) == NULL)
	            abend("too few parameters supplied to 'format'");
	         sprintf(q, fmt, (int) tt_eval(e1)->number);
	         }
	      else if (*format == 's') { /* a string */
	         if ((e1 = get_parm(e, ++parm)) == NULL)
	            abend("too few parameters supplied to 'format'");
	         sprintf(q, fmt, tt_string_of(tt_eval(e1)));
	         }
	      else if (*format == '%')
	         sprintf(q, fmt);
	      else
	         abend("invalid format character passed to 'format': %c", *format);
	      q += strlen(q);
	      p = fmt;
	      }
	   }
	*p = '\0';
	sprintf(q, fmt);
	return(tt_string_result(result));
}

/************************************************************************/
PRIVATE	v_ptr	do_getenv(e)

e_ptr	e;

{	register	char	*p;

	p = getenv(tt_string_of(tt_eval(e)));
	return(tt_string_result(p? p : ""));
}

/************************************************************************/
PRIVATE	v_ptr	do_group()

{	register	struct	group	*gp;
	register	int	gid;

	if (gp = getgrgid(gid = getgid()))
	   return(tt_string_result(gp->gr_name));
	else
	   return(tt_int_result(gid));
}

/************************************************************************/
PRIVATE	v_ptr	do_head(e)

e_ptr	e;

{	char	*p, *s;

	p = tt_string_of(tt_eval(e));
	if (s = rindex(p, '/'))
	   *s = '\0';
	return(tt_string_result(p));
}

/************************************************************************/
PRIVATE	v_ptr	do_index(e)

{	char	*source, *target;
	int	i;

	source = tt_string_of(tt_eval(get_parm(e, 1)));
	target = tt_string_of(tt_eval(get_parm(e, 2)));
	if (source == NULL || target == NULL)
	   abend("too few parameters supplied to 'index'");
	for (i = 1; *source; source++, i++) {
	   for ( ; *source && *source != *target; source++, i++)
	      ;
	   if (strncmp(source, target, strlen(target)) == 0)
	      return(tt_int_result(i));
	   }
	return(tt_int_result(0));
}

/************************************************************************/
PRIVATE	v_ptr	do_is_open()

{
	return(tt_int_result(window_get(tt_base_window->frame, FRAME_CLOSED)? 0 : 1));
}

/************************************************************************/
PRIVATE	v_ptr	do_length(e)

e_ptr	e;

{
	return(tt_int_result(strlen(tt_string_of(tt_eval(e)))));
}

/************************************************************************/
PRIVATE	v_ptr	do_output_of(e)

e_ptr	e;

{	FILE	*f;
	char	*buf, *p;
	int	amt, size;

	if ((f = popen(tt_string_of(tt_eval(e)), "r")) == NULL)
	   return(tt_int_result(-1));
	for (buf = p = tt_emalloc(65536), size = 65536; size > 0 && (amt = fread(p, sizeof(char), 1024, f)); p += amt, size -= amt)
	   ;
	*p = '\0';
	pclose(f);
	return(tt_string_result(buf));
}

/************************************************************************/
PRIVATE	v_ptr	do_pwd()

{	char	buf[1024];

	getwd(buf);
	return(tt_string_result(buf));
}

/************************************************************************/
PRIVATE	v_ptr	do_readable(e)

e_ptr	e;

{	struct	stat	buf;
	int	result;
	char	*p;

	if (stat(p = tt_string_of(tt_eval(e)), &buf) == 0 && access(p, R_OK) == 0)
	   result = 1;
	else
	   result = 0;
	return(tt_int_result(result));
}

/************************************************************************/
PRIVATE	v_ptr	do_root(e)

e_ptr	e;

{	char	*s, *p, *q;

	p = tt_string_of(tt_eval(e));
	s = rindex(p, '/');
	q = rindex(p, '.');
	if (s) {
	   if (q > s)
	      *q = '\0';
	   }
	else if (q)
	   *q = '\0';
	return(tt_string_result(p));
}

/************************************************************************/
PRIVATE	v_ptr	do_selection(e)

e_ptr	e;

{
	return(tt_string_result(tt_get_selection((int) tt_eval(e)->number)));
}

/************************************************************************/
PRIVATE	v_ptr	do_stat(e)

e_ptr	e;

{	register	v_ptr	v;
	struct	stat	buf;
	register	struct	passwd	*pp;
	register	struct	group	*gp;

	v = (v_ptr) tt_emalloc(sizeof(v_data));
	v->kind = V_ARRAY;
	v->index = NULL;
	v->value = NULL;
	v->left = NULL;
	v->right = NULL;
	if (stat(tt_string_of(tt_eval(e)), &buf) == 0) {
	   tt_insert_array(&(v->value), estrsave("mode"), tt_int_result(buf.st_mode));
	   if (pp = getpwuid(buf.st_uid))
	      tt_insert_array(&(v->value), estrsave("uid"), tt_string_result(pp->pw_name));
	   else
	      tt_insert_array(&(v->value), estrsave("uid"), tt_int_result(buf.st_uid));
	   if (gp = getgrgid(buf.st_gid))
	      tt_insert_array(&(v->value), estrsave("gid"), tt_string_result(gp->gr_name));
	   else
	      tt_insert_array(&(v->value), estrsave("gid"), tt_int_result(buf.st_gid));
	   tt_insert_array(&(v->value), estrsave("size"), tt_int_result(buf.st_size));
	   tt_insert_array(&(v->value), estrsave("atime"), tt_string_result(fix_ctime(&(buf.st_atime))));
	   tt_insert_array(&(v->value), estrsave("mtime"), tt_string_result(fix_ctime(&(buf.st_mtime))));
	   tt_insert_array(&(v->value), estrsave("ctime"), tt_string_result(fix_ctime(&(buf.st_ctime))));
	   }
	return(v);
}

/************************************************************************/
PRIVATE	v_ptr	do_substr(e)

e_ptr	e;

{	e_ptr	string, start, length;
	char	*s;
	int	st, l;

	string = get_parm(e, 1);
	start = get_parm(e, 2);
	length = get_parm(e, 3);
	if (get_parm(e, 4))
	   abend("too many arguments passed to 'substr'");
	s = estrsave(tt_string_of(tt_eval(string)));
	if ((st = start? tt_eval(start)->number - 1 : 0) < 0)
	   abend("negative starting position passed to 'substr': %d", st);
	if ((l = length? tt_eval(length)->number : 0x7fffffff) < 0)
	   abend("negative length passed to 'substr': %d", l);
	if (st > strlen(s))
	   *s = '\0';
	else
	   s += st;
	if (l <= strlen(s))
	   *(s + l) = '\0';
	return(tt_string_result(s));
}

/************************************************************************/
PRIVATE	v_ptr	do_suffix(e)

e_ptr	e;

{	char	*s, *p, *q;

	p = tt_string_of(tt_eval(e));
	s = rindex(p, '/');
	q = rindex(p, '.');
	if (s)
	   p = (q > s)? q + 1 : "";
	else
	   p = q? q + 1 : "";
	return(tt_string_result(p));
}

/************************************************************************/
PRIVATE	v_ptr	do_system(e)

e_ptr	e;

{
	return(tt_int_result(system(tt_string_of(tt_eval(e)))));
}

/************************************************************************/
PRIVATE	v_ptr	do_tail(e)

e_ptr	e;

{	char	*p, *s;

	p = tt_string_of(tt_eval(e));
	if (s = rindex(p, '/'))
	   p = s + 1;
	return(tt_string_result(p));
}

/************************************************************************/
PRIVATE	v_ptr	do_tokenize(e)

e_ptr	e;

{	register	char	**tokens, *line;
	register	int	i, max_count;
	register	v_ptr	v;
	char	buf[20];
	int	count;

	line = tt_string_of(tt_eval(e));
	tokens = (char **) tt_emalloc((max_count = strlen(line) / 2 + 2) * sizeof(char *));
	tokenize(line, &count, tokens, max_count);
	v = (v_ptr) tt_emalloc(sizeof(v_data));
	v->kind = V_ARRAY;
	v->index = NULL;
	v->value = NULL;
	v->left = NULL;
	v->right = NULL;
	for (i = 0; i < count; i++) {
	   sprintf(buf, "%d", i);
	   tt_insert_array(&(v->value), estrsave(buf), tt_string_result(tokens[i]));
	   }
	return(v);
}

/************************************************************************/
PRIVATE	v_ptr	do_user()

{	register	struct	passwd	*pp;
	register	int	uid;

	if (pp = getpwuid(uid = getuid()))
	   return(tt_string_result(pp->pw_name));
	else
	   return(tt_int_result(uid));
}

/************************************************************************/
PRIVATE	v_ptr	do_verify(e)

{	char	*source, *valid;

	source = tt_string_of(tt_eval(get_parm(e, 1)));
	valid = tt_string_of(tt_eval(get_parm(e, 2)));
	if (source == NULL || valid == NULL)
	   abend("too few parameters supplied to 'verify'");
	for ( ; *source; source++)
	   if (index(valid, *source) == NULL)
	      return(tt_int_result(0));
	return(tt_int_result(1));
}

/************************************************************************/
PRIVATE	v_ptr	do_writable(e)

e_ptr	e;

{	struct	stat	buf;
	int	result;
	char	*p;

	if (stat(p = tt_string_of(tt_eval(e)), &buf) == 0 && access(p, W_OK) == 0)
	   result = 1;
	else
	   result = 0;
	return(tt_int_result(result));
}
