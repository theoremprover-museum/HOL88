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

#include	"tooltool.h"

#define		MIN_BUF_SIZE	32768

typedef	struct	em_rec	em_data, *em_ptr;

struct	em_rec	{int	size;
		 int	remaining;
		 char	*buf;
		 em_ptr	next;
		};

PRIVATE	em_ptr	buf_list = NULL;

/************************************************************************/
EXPORT	char	*tt_emalloc(size)

int	size;

{	em_ptr	em;
	char	*p;

	size = ((size + 3) & ~3);
	for (em = buf_list; em; em = em->next)
	   if (em->remaining >= size)
	      break;
	if (em == NULL) {
	   em = (em_ptr) safe_malloc(sizeof(em_data));
	   em->size = em->remaining = max(size, MIN_BUF_SIZE);
	   em->buf = (char *) safe_malloc(em->size);
	   em->next = buf_list;
	   buf_list = em;
	   }
	p = em->buf + em->size - em->remaining;
	em->remaining -= size;
	return(p);
}

/************************************************************************/
EXPORT	tt_reset_emalloc()

{	em_ptr	em;

	for (em = buf_list; em; em = em->next)
	   em->remaining = em->size;
}

/************************************************************************/
EXPORT	int	tt_is_temp(p)

char	*p;

{	em_ptr	em;

	for (em = buf_list; em; em = em->next)
	   if (p >= em->buf && p <= em->buf + em->size)
	      return(TRUE);
	return(FALSE);
}
