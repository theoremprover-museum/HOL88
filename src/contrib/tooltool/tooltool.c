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

#include	<sys/file.h>

#include	"tooltool.h"

EXPORT	a_ptr	tt_initial_action = NULL,
		tt_timer_action = NULL,
		tt_func_keys[MAX_KEY_SETS][MAX_FUNC_KEYS][MAX_SHIFT_SETS];

EXPORT	char	*tt_application = NULL,
		*tt_curr_file = "stdin",
		*tt_icon = NULL,
		*tt_program;

EXPORT	d_ptr	tt_base_window = NULL;

EXPORT	int	tt_mouse_base = 0,
		tt_mouse_chars = TRUE,
		tt_errors_occured = 0,
		tt_normal_off = FALSE,
		tt_function_off = FALSE,
		tt_action_depth = 0,
		tt_timer_pending = FALSE;

EXPORT	l_ptr	tt_default_mark,
		tt_default_nomark,
		tt_default_cycle;

EXPORT	m_data	tt_mouse[MAX_MOUSE_BUTTONS][MAX_SHIFT_SETS];

EXPORT	Menu	tt_ttymenu = NULL;

EXPORT	struct	pixfont	*tt_default_font = NULL,
			*tt_a_font = NULL;

EXPORT	s_ptr	tt_mouse_x,
		tt_mouse_y,
		tt_delimiters;

PRIVATE	short	mark_bits[] = {0x07C0,0x1830,0x2008,0x4384,0x4FE4,0x8FE2,0x9FF2,0x9FF2,
			       0x9FF2,0x8FE2,0x4FE4,0x4384,0x2008,0x1830,0x07C0,0x0000};
mpr_static(tt_mark_image, 15, 15, 1, mark_bits);

PRIVATE	short	nomark_bits[] = {0x07C0,0x1830,0x2008,0x4004,0x4004,0x8002,0x8002,0x8002,
				 0x8002,0x8002,0x4004,0x4004,0x2008,0x1830,0x07C0,0x0000};
mpr_static(tt_nomark_image, 15, 15, 1, nomark_bits);

PRIVATE	short	cycle_bits[] = {0x07C0,0x0FE0,0x1834,0x301C,0x601C,0x203C,0x0000,0x0000,
				0x7808,0x700C,0x7018,0x5830,0x0FE0,0x07C0,0x0000,0x0000};
mpr_static(tt_cycle_image, 16, 16, 1, cycle_bits);

/************************************************************************/
/* The main driver parses the specification file, builds the window,	*/
/* and starts up suntools to execute the user application.		*/
/************************************************************************/

/************************************************************************/
PRIVATE	check_args(argc, argv, n1, n2, v1, v2)

int	*argc;
char	**argv;
char	*n1;
char	*n2;
int	*v1;
int	*v2;

{	int	i, j;

	for (i = 1; i < *argc; i++)
	   if (strcmp(argv[i], n1) == 0 || strcmp(argv[i], n2) == 0) {
	      if (i + 1 < *argc)
	         *v1 = atoi(argv[i + 1]);
	      else
	         abend("missing argument after %s", argv[i]);
	      if (v2)
	         if (i + 2 < *argc)
	            *v2 = atoi(argv[i + 2]);
	         else
	            abend("missing argument after %s", argv[i]);
	      for (j = i + (v2? 3 : 2); j < *argc; j++, i++)
	         argv[i] = argv[j];
	      *argc -= (v2? 3 : 2);
	      argv[*argc] = NULL;
	      break;
	      }
}

/************************************************************************/
main(argc, argv)

int	argc;
char	**argv;

{	int	i, j, k;
	int	force_height = -1, force_width = -1, force_rows = -1, force_cols = -1;

	tt_program = strsave(argv[0]);

	if (argc > 1 && strcmp(argv[1], POLLING_MAGIC_NUMBER) == 0) { /* is this a gross hack, or what? */
	   wait_for_window_size(atoi(argv[2]), atoi(argv[3]), POLLING_TIME_OUT);
	   execv(tt_full_path_of(argv[4], X_OK), &(argv[4]));
	   fprintf(stderr, "could not exec %s\n", argv[4]);
	   sleep(20);
	   exit(1);
	   }

	for (i = LEFT_KEY_SET; i < MAX_KEY_SETS; i++)
	   for (j = 0; j < MAX_FUNC_KEYS; j++)
	      for (k = 0; k < MAX_SHIFT_SETS; k++)
	         tt_func_keys[i][j][k] = NULL;
	for (i = MOUSE_LEFT; i < MAX_MOUSE_BUTTONS; i++)
	   for (j = 0; j < MAX_SHIFT_SETS; j++)
	      tt_mouse[i][j].defined = MOUSE_UNDEFINED;

	if (argc >= 3 && strcmp(argv[1], "-f") == 0) {
	   if (freopen(tt_full_path_of(argv[2], R_OK), "r", stdin) == NULL)
	      abend("could not read %s", argv[2]);
	   else {
	      tt_curr_file = argv[2];
	      for (i = 3; i < argc; i++)
	         argv[i - 2] = argv[i];
	      argc -= 2;
	      }
	   }
	check_args(&argc, argv, "-Ww", "-width", &force_cols, NULL);
	check_args(&argc, argv, "-Wh", "-height", &force_rows, NULL);
	check_args(&argc, argv, "-Ws", "-size", &force_width, &force_height);

	tt_default_font = pf_default();
	tt_default_mark = tt_make_label(FALSE, NULL, NULL, &tt_mark_image);
	tt_default_nomark = tt_make_label(FALSE, NULL, NULL, &tt_nomark_image);
	tt_default_cycle = tt_make_label(FALSE, NULL, NULL, &tt_cycle_image);
	tt_a_font = tt_default_font;
	tt_base_window = tt_make_base_window();
	tt_make_intrinsic_symbols();
	yyparse();
	if (tt_errors_occured)
	   abend("%d errors.", tt_errors_occured);
	if (force_height != -1)
	   if (force_rows != -1 || force_cols != -1)
	      abend("conflict between window size command line options");
	   else {
	      tt_base_window->is_chars = FALSE;
	      tt_base_window->rows = force_height;
	      tt_base_window->columns = force_width;
	      }
	else {
	   if (force_rows != -1)
	      if (tt_base_window->is_chars)
	         tt_base_window->rows = force_rows;
	      else
	         tt_base_window->rows = force_rows * charheight_of(tt_a_font);
	   if (force_cols != -1)
	      if (tt_base_window->is_chars)
	         tt_base_window->columns = force_cols;
	      else
	         tt_base_window->columns = force_cols * charwidth_of(tt_a_font);
	   }
	if (tt_base_window->g_align == NO_ALIGN)
	   tt_base_window->g_align = ALIGN_TOP;
	build_window(argc, argv);
	window_main_loop(tt_base_window->frame);
	exit(0);
}
