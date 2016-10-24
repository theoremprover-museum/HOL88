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
#include	<sgtty.h>
#include	<pwd.h>

#include	<sys/types.h>
#include	<sys/stat.h>
#include	<sys/dir.h>
#include	<sys/file.h>

#include	<suntool/sunview.h>
#include	<suntool/icon_load.h>

#include	"tooltool.h"

PUBLIC	char	*index(), *rindex(), *getenv();

typedef	struct	pc_rec	pc_data, *pc_ptr;
typedef	struct	fc_rec	fc_data, *fc_ptr;

struct	pc_rec	{char	*path;
		 struct	pixrect	*image;
		 pc_ptr	next;
		};

struct	fc_rec	{char	*path;
		 struct	pixfont	*font;
		 fc_ptr	next;
		};

PRIVATE	pc_ptr	pix_cache = NULL;
PRIVATE	fc_ptr	font_cache = NULL;

/************************************************************************/
EXPORT	char	*safe_malloc(size)

int	size;

{	char	*p;

	if (p = (char *) malloc(size))
	   return(p);
	else
	   abend("insufficient memory available");
}

/************************************************************************/
EXPORT	safe_free(p)

char	*p;

{
	free(p);
}

/************************************************************************/
EXPORT	tokenize(line, argc, argv, maxv)

char	*line;
int	*argc;
char	*argv[];
int	maxv;

{	char	*buf, match, *delimiters;

	*argc = 0;
	buf = (char *) tt_emalloc(strlen(line) * 2 + 1);
	if ((delimiters = tt_string_of(tt_delimiters->value)) == NULL)
	   delimiters = " \t\n\r\"'";
	while (*line && (*argc < (maxv - 1))) {
	   while (*line && index(delimiters, *line))
	      if (*line == '"' || *line == '\'')
	         break;
	      else
	         line++;
	   if (*line == '\0')
	      break;
	   argv[(*argc)++] = buf;
	   if (index(delimiters, *line)) { /* scanning a quoted string */
	      match = *line++; /* remove the quote mark */
	      while (*line && (*line != match))
	         *buf++ = *line++;
	      if (*line)
	         line++; /* wipe out quote mark */
	      }
	   else {
	      while (*line && !index(delimiters, *line))
	         *buf++ = *line++;
	      }
	   *buf++ = '\0';
	   }
	*buf = '\0';
	argv[*argc] = (char *) 0;
}

/************************************************************************/
EXPORT	struct	pixrect	*tt_load_icon(path)

char	*path;

{	char	msg[IL_ERRORMSG_SIZE];
	struct	pixrect	*p;
	FILE	*f;
	pc_ptr	pc;

	for (pc = pix_cache; pc; pc = pc->next)
	   if (strcmp(path, pc->path) == 0)
	      return(pc->image);
	if ((p = icon_load_mpr(path, msg)) == NULL) { /* not in icon format */
	   if ((f = fopen(path, "r")) == NULL)
	      abend("could not open %s", path);
	   if ((p = pr_load(f, NULL)) == NULL)
	      abend("%s must be in either icon or raster file format", path);
	   fclose(f);
	   }
	pc = (pc_ptr) safe_malloc(sizeof(pc_data));
	pc->path = strsave(path);
	pc->image = p;
	pc->next = pix_cache;
	pix_cache = pc;
	return(p);
}

/************************************************************************/
EXPORT	struct	pixfont	*tt_open_font(path)

char	*path;

{	struct	pixfont	*p;
	fc_ptr	pf;

	for (pf = font_cache; pf; pf = pf->next)
	   if (strcmp(path, pf->path) == 0)
	      return(pf->font);
	if ((p = pf_open(path)) == NULL)
	   abend("cannot open font: %s", path);
	pf = (fc_ptr) safe_malloc(sizeof(fc_data));
	pf->path = strsave(path);
	pf->font = p;
	pf->next = font_cache;
	font_cache = pf;
	return(p);
}

/************************************************************************/
EXPORT	int	text_width(text, font)

unsigned	char	*text;
struct	pixfont	*font;

{	int	width;

	for (width = 0; *text; text++)
	   width += font->pf_char[*text].pc_adv.x;
	return(width);
}

/************************************************************************/
PRIVATE	char	*root_path(path)

char	*path;

{	char	*p;

	if (p = rindex(path, '/'))
	   if (p == path)
	      p[1] = '\0';
	   else
	      *p = '\0';
	else
	   *path = '\0';
	return(path);
}

/************************************************************************/
PRIVATE	char	*last_node(path)

char	*path;

{	char	*p;

	return((p = rindex(path, '/'))? p + 1 : path);
}

/************************************************************************/
EXPORT	char	*expand_filename(path)

char	*path;

{	static	char	s[1024];
	char	pattern[1024], candidate[1024], *p,*q;
	DIR	*dir;
	struct	direct *dp;
	struct	passwd	*pw;

	strcpy(s, path);
	if (*path == '~')
	   if (path[1] == '/' || path[1] == '\0') {
	      strcpy(s, getenv("HOME"));
	      strcat(s, path + 1);
	      }
	   else {
	      if ((p = index(path, '/')) != NULL)
	         *p = '\0';
	      if ((pw = getpwnam(path + 1)) != NULL) {
	         strcpy(s, pw->pw_dir);
	         if (p != NULL) {
	            strcat(s, "/");
	            strcat(s, p + 1);
	            }
	         }
	      else
	         return(NULL);
	      }
	strcpy(pattern, last_node(s));
	if (*pattern == '\0')
	   return(s);
	root_path(s);
	candidate[0] = '\0';
	if (*s == '\0')
	   strcpy(s, ".");
	if ((dir = opendir(s)) == NULL) {
	   strcpy(s, path);
	   return(s);
	   }
	while ((dp = readdir(dir)) != NULL)
	   if (strncmp(dp->d_name, pattern, strlen(pattern)) == 0)
	      if (*candidate == '\0')
	         strcpy(candidate, dp->d_name);
	      else {
	         for (p = candidate, q = dp->d_name; *p == *q; p++, q++)
	            ;
	         *p = '\0';
	         }
	closedir(dir);
	if (*candidate == '\0')
	   return(NULL);
	else {
	   if (strcmp(s, ".") == 0)
	      *s = '\0';
	   else if (s[strlen(s) - 1] != '/')
	      strcat(s, "/");
	   strcat(s, candidate);
	   }
	return(s);
}

/************************************************************************/
EXPORT	tt_construct_label(l)

l_ptr	l;

{	struct	pr_prpos	where;

	if (!l->is_icon && l->image == NULL) {
	   l->image = mem_create(text_width(l->label, l->font), l->font->pf_defaultsize.y, 1);
	   where.pr = l->image;
	   where.pos.x = 0;
	   where.pos.y = baseline_of(l->font);
	   pf_text(where, PIX_SRC, l->font, l->label);
	   }
}

/************************************************************************/
EXPORT	l_ptr	tt_make_label(is_icon, label, font, image)

int	is_icon;
char	*label;
Pixfont	*font;
struct	pixrect	*image;

{	l_ptr	l;

	l = (l_ptr) safe_malloc(sizeof(l_data));
	l->is_icon = is_icon;
	l->label = label;
	l->font = font;
	l->image = image;
	return(l);
}

/************************************************************************/
EXPORT	d_ptr	tt_make_base_window()

{	d_ptr	d;

	d = (d_ptr) safe_malloc(sizeof(d_data));
	d->frame = NULL;
	d->panel = NULL;
	d->is_base_frame = FALSE;
	d->is_open = TRUE;
	d->is_popup = FALSE;
	d->rows = 24;
	d->columns = 80;
	d->win_x = -1;
	d->win_y = -1;
	d->is_chars = TRUE;
	d->g_align = NO_ALIGN;
	d->proportional = FALSE;
	d->justified = TRUE;
	d->text_items_exist = FALSE;
	d->gadget_pos = G_NOPOS;
	d->gadgets = NULL;
	d->label = NULL;
	d->open_action = NULL;
	d->close_action = NULL;
	d->g_font = tt_default_font;
	d->next = NULL;
	return(d);
}

/************************************************************************/
EXPORT	abend(s1, s2, s3, s4, s5, s6, s7, s8, s9)

char	*s1, *s2, *s3, *s4, *s5, *s6, *s7, *s8, *s9;

{
	fprintf(stderr, "%s: ", tt_program);
	fprintf(stderr, s1, s2, s3, s4, s5, s6, s7, s8, s9);
	fprintf(stderr, "\n");
	exit(1);
}

/************************************************************************/
EXPORT	int	tt_is_number(s)

register	char	*s;

{	register	int	saw_digit = FALSE;

	if (*s == '-' || *s == '+')
	   s++;
	for ( ; isdigit(*s); s++)
	   saw_digit = TRUE;
	if (*s == '.')
	   for (s++; isdigit(*s); s++)
	      saw_digit = TRUE;
	if (*s == 'e' || *s == 'E') {
	   if (*++s == '-' || *s == '+')
	      s++;
	   for ( ; isdigit(*s); s++)
	      saw_digit = TRUE;
	   }
	return(saw_digit && *s == '\0');
}

/************************************************************************/
EXPORT	int	tt_dict_compare(l, r)

char	*l;
char	*r;

{	register	char	*p, *q;

	for (p = l; isdigit(*p); p++)
	   ;
	for (q = r; isdigit(*q); q++)
	   ;
	if (*p || *q)
	   return(strcmp(l, r));
	else
	   return(atoi(l) - atoi(r));
}

/************************************************************************/
EXPORT	char	*tt_expand_ranges(s)

unsigned	char	*s;

{	unsigned	char	*p, buf[1024];
	int	c;

	for (p = buf; *s; s) {
	   *p++ = *s++;
	   if (*s == '-' && *(s + 1) != '\0') {
	      for (c = *(p - 1), s++; c <= *s; )
	         *p++ = c++;
	      s++;
	      }
	   }
	*p = '\0';
	return(strsave(buf));
}

/************************************************************************/
EXPORT	wait_for_window_size(width, height, timeout)

int	width;
int	height;
int	timeout; /* in milliseconds */

{	struct	winsize	win;

	if (width > 0 && height > 0)
	   do {
	      if (ioctl(fileno(stderr), TIOCGWINSZ, &win) < 0)
	         abend("could not obtain the window size");
	      usleep(50000);
	      } while ((win.ws_row != height || win.ws_col != width) && (timeout -= 50) > 0);
}

/************************************************************************/
EXPORT	int	tt_perm_of(st)

struct	stat	*st;

{
	if (getuid() == st->st_uid)
	   return((st->st_mode & 0700) >> 6);
	else if (getgid() == st->st_gid)
	   return((st->st_mode & 070) >> 3);
	else
	   return((st->st_mode & 07));
}

/************************************************************************/
EXPORT	char	*tt_full_path_of(s, mode)

char	*s;
int	mode;

{	char	*path, *p, *q;
	static	char	full_path[1024];
	struct	stat	buf;

	if (*s == '/')
	   return(s);
	path = getenv("PATH");
	for (p = path, q = full_path; TRUE; )
	   if (*p == ':' || *p == '\0') {
	      *q = '\0';
	      strcat(full_path, "/");
	      strcat(full_path, s);
	      if (stat(full_path, &buf) == 0 && ((buf.st_mode & S_IFMT) == S_IFREG) && access(full_path, mode) == 0)
	         return(full_path);
	      q = full_path;
	      if (*p++ == '\0')
	         return(s);
	      }
	   else
	      *q++ = *p++;
}
