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
#include	<sys/types.h>
#include	<suntool/selection_svc.h>
#include	<suntool/selection_attributes.h>

#include	"tooltool.h"

PRIVATE	Seln_result	read_proc();

PRIVATE	char	*buf, *pos;

EXPORT	char	*tt_get_selection(level)

int	level;

{	Seln_client	client;
	Seln_holder	holder;
	Seln_rank	rank;
	char		context = 0;

	if (level == 1)
	   rank = SELN_PRIMARY;
	else if (level == 2)
	   rank = SELN_SECONDARY;
	else if (level == 3)
	   rank = SELN_SHELF;
	else
	   return("");
	holder = seln_inquire(rank);
	if (holder.state == SELN_NONE)
	   return("");
	pos = buf = tt_emalloc(65536);
	*buf = '\0';
	seln_query(&holder, read_proc, &context, SELN_REQ_CONTENTS_ASCII, 0, 0);
	return(buf);
}

PRIVATE	Seln_result	read_proc(buffer)

Seln_request	*buffer;

{	char	*reply;

	if (buffer) {
	   if (*buffer->requester.context == 0) {
	      if (*((Seln_attribute *) buffer->data) != SELN_REQ_CONTENTS_ASCII)
	         return(SELN_FAILED);
	      reply = buffer->data + sizeof(Seln_attribute);
	      *buffer->requester.context = 1;
	      }
	   else
	      reply = buffer->data;
	   strcpy(pos, reply);
	   pos += strlen(reply);
	   }
	return(SELN_SUCCESS);
}
