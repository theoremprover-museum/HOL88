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


#include	<suntool/sunview.h>
#include	<suntool/panel.h>

/* Help delineate where routines are used and defined
 */
#define		PUBLIC			extern
#define		PRIVATE			static
#define		EXPORT

#define		strsave(s)		((char *) strcpy((char *) safe_malloc(strlen(s) + 1), s))
#define		estrsave(s)		((char *) strcpy((char *) tt_emalloc(strlen(s) + 1), s))
#define		baseline_of(f)		(-((f)->pf_char['0'].pc_home.y))
#define		charwidth_of(f)		((f)->pf_char['0'].pc_adv.x)
#define		charheight_of(f)	((f)->pf_defaultsize.y)
#define		value_of(v)		((v)->is_number? (v)->number : 0.0)

/* The gadget position possibilities
 */
#define		G_NOPOS			-1
#define		G_TOP			0
#define		G_BOTTOM		1
#define		G_LEFT			2
#define		G_RIGHT			3

/* The shift states available for various function keys
 */
#define		S_NORMAL		0
#define		S_SHIFT			1
#define		S_CONTROL		2
#define		S_META			4
#define		MAX_SHIFT_SETS		8

/* The kind of gadgets we can create
 */
#define		GADGET_BUTTON		0
#define		GADGET_CHOICE		1
#define		GADGET_LABEL		2
#define		GADGET_MENU		3
#define		GADGET_SLIDER		4
#define		GADGET_TEXT		5

/* Special functions that gadgets can perform
 */
#define		BEEP_OP			0
#define		BREAK_OP		1
#define		CLOSE_OP		2
#define		CONTINUE_OP		3
#define		DISPLAY_OP		4
#define		EXIT_OP			5
#define		EXPR_OP			6
#define		FOR_OP			7
#define		IF_OP			8
#define		OPEN_OP			9
#define		POPUP_OP		10
#define		REMOVE_OP		11
#define		SEND_OP			12
#define		WHILE_OP		13

/* How labels are aligned with respect to each other
 */
#define		NO_ALIGN		0
#define		ALIGN_TOP		1
#define		ALIGN_MIDDLE		2
#define		ALIGN_BOTTOM		3

/* The different function key sets on a Sun-3 keyboard
 */
#define		LEFT_KEY_SET		0
#define		TOP_KEY_SET		1
#define		RIGHT_KEY_SET		2
#define		MAX_KEY_SETS		3

#define		MAX_FUNC_KEYS		15

/* Mouse buttons
 */
#define		MOUSE_LEFT		0
#define		MOUSE_CENTER		1
#define		MOUSE_RIGHT		2

#define		MAX_MOUSE_BUTTONS	3

/* The functions a mouse key can perform
 */
#define		MOUSE_UNDEFINED		0
#define		MOUSE_STRING		1
#define		MOUSE_MENU		2

/* The ways a choice gadget can be laid out
 */
#define		CHOICE_CURRENT		0
#define		CHOICE_CYCLE		1
#define		CHOICE_HORIZONTAL	2
#define		CHOICE_VERTICAL		3

/* The kinds of symbols a user can define
 */
#define		SYMBOL_SYMBOL		0
#define		SYMBOL_GADGET		1
#define		SYMBOL_DIALOG		2

/* Various expression operators
 */
#define		E_AND			0
#define		E_ARRAY_REF		1
#define		E_ASSIGN_AND		2
#define		E_ASSIGN_DIVIDE		3
#define		E_ASSIGN_MINUS		4
#define		E_ASSIGN_MODULO		5
#define		E_ASSIGN_OR		6
#define		E_ASSIGN_PLUS		7
#define		E_ASSIGN_TIMES		8
#define		E_ASSIGN_XOR		9
#define		E_ASSIGNMENT		10
#define		E_COMMA			11
#define		E_COMPLEMENT		12
#define		E_DIVIDE		13
#define		E_EQUAL			14
#define		E_FUNC_ID		15
#define		E_GREATER		16
#define		E_GREATER_EQUAL		17
#define		E_LEFT_SHIFT		18
#define		E_LESS			19
#define		E_LESS_EQUAL		20
#define		E_LOGICAL_AND		21
#define		E_LOGICAL_NOT		22
#define		E_LOGICAL_OR		23
#define		E_MINUS			24
#define		E_MODULO		25
#define		E_NOT_EQUAL		26
#define		E_NUMBER		27
#define		E_OR			28
#define		E_PAREN			29
#define		E_PLUS			30
#define		E_POSTDECREMENT		31
#define		E_POSTINCREMENT		32
#define		E_PREDECREMENT		33
#define		E_PREINCREMENT		34
#define		E_QUESTION		35
#define		E_RIGHT_SHIFT		36
#define		E_STRING		37
#define		E_SYMBOL		38
#define		E_TIMES			39
#define		E_UMINUS		40
#define		E_XOR			41

/* The kinds of values we can express.
 */
#define		V_NOTHING		0
#define		V_ARRAY			1
#define		V_GADGET		2
#define		V_NUMBER		4
#define		V_INTERVAL		8

#define		V_TYPES			(V_ARRAY | V_NUMBER)
#define		V_SPECIAL		(V_GADGET | V_INTERVAL)

#define		is_array(v)		((v)->kind & V_ARRAY)
#define		is_gadget(v)		((v)->kind & V_GADGET)
#define		is_number(v)		((v)->kind & V_NUMBER)
#define		is_interval(v)		((v)->kind & V_INTERVAL)

/* Special things used to beat a Suntools window size bug
 */
#define		POLLING_MAGIC_NUMBER	"\001\002\003\004"
#define		POLLING_TIME_OUT	20000 /* milliseconds */

/* The data necessary to describe a label.  If "is_icon" is FALSE,
 * "label" holds the label text, and "font" holds the label font.
 * If TRUE, "image" holds the bitmap of the icon for the label.
 */
typedef	struct	l_rec	l_data, *l_ptr;

struct	l_rec	{int	is_icon;
		 char	*label;
		 struct	pixfont	*font;
		 struct	pixrect	*image;
		};

/* The data needed to describe a gadget.  "Kind" is one of 
 * GADGET_*, above, and indicates which portion of the union
 * is valid for this gadget.  "Image" contains the image bitmap
 * for buttons and menus, and labels if they are icons.  Sliders
 * and choices have their own, SunView-created, images.  For all
 * gadgets, "width" and "height" are set to reflect the image
 * bounding box, for gadget layout purposes.  The gadgets are 
 * linked together via "next".
 */

typedef	struct	a_rec	a_data, *a_ptr;
typedef	struct	cv_rec	cv_data, *cv_ptr;
typedef struct	d_rec	d_data, *d_ptr;
typedef	struct	e_rec	e_data, *e_ptr;
typedef	struct	g_rec	g_data, *g_ptr;
typedef	struct	s_rec	s_data, *s_ptr;
typedef	struct	v_rec	v_data, *v_ptr;

typedef	v_ptr	(*f_ptr)();

struct	but_rec	{l_ptr	label[MAX_SHIFT_SETS];
		 a_ptr	action[MAX_SHIFT_SETS];
		 Menu	menu;
		};

struct	cv_rec	{l_ptr	label;
		 a_ptr	action;
		 cv_ptr	next;
		};

struct	cho_rec	{l_ptr	label;
		 int	mode;
		 int	ch_width;
		 int	ch_height;
		 l_ptr	mark;
		 l_ptr	nomark;
		 cv_ptr	value;
		};

struct	lab_rec	{l_ptr	label;
		};

struct	men_rec	{l_ptr	label;
		 Menu	menu;
		};

struct	sli_rec	{l_ptr	label;
		 int	minimum;
		 int	maximum;
		 int	initial;
		 int	value;
		 int	range;
		 int	width;
		 a_ptr	action;
		 struct	pixfont	*font;
		};

struct	tex_rec	{l_ptr	label;
		 char	*trigger;
		 char	*completion;
		 char	*ignore;
		 int	display_len;
		 int	retain_len;
		 a_ptr	action; 
		 struct	pixfont	*font;
		};

struct	g_rec	{int	kind;
		 char	*name;
		 Panel_item	panel_item;
		 struct	pixrect	*image;
		 int	width;
		 int	height;
		 int	x;
		 int	y;
		 g_ptr	next;
		 union	{struct	but_rec	but;
		 	 struct	cho_rec	cho;
		 	 struct	lab_rec	lab;
		 	 struct	men_rec	men;
		 	 struct	sli_rec	sli;
		 	 struct	tex_rec	tex;
		 	} u;
		};

/* The data necessary to describe an action.
 */
struct	a_rec	{int	op;
		 e_ptr	init;
		 e_ptr	expr;
		 e_ptr	term;
		 a_ptr	body;
		 a_ptr	else_part;
		 a_ptr	next;
		};

/* The data necessary to describe an expression
 */
struct	e_rec	{int	op;
		 e_ptr	left;
		 e_ptr	right;
		 e_ptr	extra;
		 s_ptr	symbol;
		 char	*string;
		 double	value;
		 f_ptr	func;
		};

/* The data necessary to describe a value
 */
struct	v_rec	{int	kind;
		 char	*str;	/* except when an array */
		 double	number;	/* if a number */
		 g_ptr	gadget;	/* if a gadget */
		 char	*index; /* array element index string */
		 v_ptr	value;	/* if an array */
		 v_ptr	left;	/* links for array element tree */
		 v_ptr	right;
		};

/* The data necessary to describe a symbol.
 */
struct	s_rec	{int	kind;
		 char	*name;
		 g_ptr	gadget;		/* if a gadget */
		 d_ptr	dialog;		/* if a dialog */
		 v_ptr	value;		/* if a symbol */
		 s_ptr	left;
		 s_ptr	right;
		};

/* The data necessary to describe a panel
 */
struct	d_rec	{Frame	frame;
		 Panel	panel;
		 int	is_base_frame;
		 int	is_open;
		 int	is_popup;
		 int	rows;
		 int	columns;
		 int	win_x;
		 int	win_y;
		 int	is_chars;
		 int	g_align;
		 int	proportional;
		 int	justified;
		 int	text_items_exist;
		 int	gadget_pos;
		 g_ptr	gadgets;
		 char	*label;
		 a_ptr	open_action;
		 a_ptr	close_action;
		 struct	pixfont	*g_font;
		 d_ptr	next;
		};

/* A mouse record holds operation to be performed by one mouse
 * button/shift-state combination.  "Defined" is one of 
 * MOUSE_{UNDEFINED,STRING,MENU}.  If MOUSE_STRING, "value" holds
 * the text to be transmitted.  If MOUSE_MENU, "menu" holds
 * the menu to be displayed.
 */
typedef	struct	m_rec	m_data;

struct	m_rec	{int	defined;
		 a_ptr	action;
		 Menu	menu;
		};

/* A variety of public data.  All globals begin with "tt_".
 */
PUBLIC	a_ptr	tt_initial_action,
		tt_timer_action,
		tt_func_keys[MAX_KEY_SETS][MAX_FUNC_KEYS][MAX_SHIFT_SETS];

PUBLIC	char	*tt_application,
		*tt_curr_file,
		*tt_icon,
		*tt_program;

PUBLIC	d_ptr	tt_base_window;

PUBLIC	int	tt_mouse_base,
		tt_mouse_chars,
		tt_errors_occured,
		tt_normal_off,
		tt_function_off,
		tt_action_depth,
		tt_timer_pending;

PUBLIC	l_ptr	tt_default_mark,
		tt_default_nomark,
		tt_default_cycle;

PUBLIC	m_data	tt_mouse[MAX_MOUSE_BUTTONS][MAX_SHIFT_SETS];

PUBLIC	Menu	tt_ttymenu;

PUBLIC	struct	pixfont	*tt_default_font,
			*tt_a_font;

PUBLIC	struct	pixrect	tt_mark_image,
			tt_nomark_image,
			tt_cycle_image;

PUBLIC	s_ptr	tt_mouse_x, tt_mouse_y, tt_delimiters;

/* Public routines which do not return void.
 */
PUBLIC	char	*safe_malloc();
PUBLIC	struct	pixrect	*tt_load_icon();
PUBLIC	struct	pixfont	*tt_open_font();
PUBLIC	l_ptr	tt_make_label();
PUBLIC	a_ptr	tt_make_action();
PUBLIC	s_ptr	tt_find_symbol();
PUBLIC	v_ptr	tt_get_value();
PUBLIC	d_ptr	tt_make_base_window();
PUBLIC	e_ptr	tt_make_expr();
PUBLIC	v_ptr	tt_eval();
PUBLIC	char	*tt_string_of();
PUBLIC	f_ptr	tt_is_function();
PUBLIC	char	*tt_emalloc();
PUBLIC	v_ptr	tt_int_result();
PUBLIC	v_ptr	tt_double_result();
PUBLIC	v_ptr	tt_string_result();
PUBLIC	v_ptr	tt_insert_array();
PUBLIC	char	*tt_get_selection();
PUBLIC	char	*tt_expand_ranges();
PUBLIC	char	*tt_full_path_of();
