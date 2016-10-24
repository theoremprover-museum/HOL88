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

PRIVATE	short	cross_bits[] = {0x4000, 0xe000, 0x4000};
mpr_static(tt_better_button_cross, 3, 3, 1, cross_bits);

PRIVATE	short	arrow_bits[] = {0x0400, 0x0600, 0xFD00, 0x0180, 0xFD00, 0x0600, 0x0400};
mpr_static(tt_menu_arrow, 9, 7, 1, arrow_bits);

PUBLIC	event_proc(),
	notify_proc();

/************************************************************************/
/* This group of routines contructs individual panel gadgets.		*/
/************************************************************************/

/************************************************************************/
PRIVATE	struct	pixrect	*better_menu_image(text, chars, pixels, font)

char	*text;
int	chars;
int	pixels;
struct	pixfont	*font;

{	struct	pixrect	*pr;
	struct	pr_prpos	pos;
	int	width, true_width, height;

	width = chars * charwidth_of(font) + pixels;
	true_width = text_width(text, font) + 13;
	if (width < true_width)
	   width = true_width;
	pr = mem_create(width + 8, height = charheight_of(font) + 6, 1);
	pr_rop(pr, 0, 0, width + 8, height, PIX_SRC | PIX_COLOR(1), NULL, 0, 0);
	pr_rop(pr, 2, 2, width + 4, height - 4, PIX_SRC | PIX_COLOR(0), NULL, 0, 0);
	pr_rop(pr, width - 5, (height - 7) / 2, 9, 7, PIX_SRC, &tt_menu_arrow, 0, 0);
	pos.pr = pr;
	pos.pos.x = 4 + (width - true_width) / 2;
	pos.pos.y = 4 + baseline_of(font);
	pf_ttext(pos, PIX_SRC | PIX_COLOR(1), font, text);
	return(pr);
}

/************************************************************************/
PRIVATE	struct	pixrect	*better_button_image(text, chars, pixels, font)

char	*text;
int	chars;
int	pixels;
struct	pixfont	*font;

{	struct	pixrect	*pr;
	struct	pr_prpos	pos;
	int	width, true_width, height;

	width = chars * charwidth_of(font) + pixels;
	true_width = text_width(text, font);
	if (width < true_width)
	   width = true_width;
	pr = mem_create(width + 8, height = charheight_of(font) + 6, 1);
	pr_rop(pr, 3, 0, width + 2, 2, PIX_SRC | PIX_COLOR(1), NULL, 0, 0);
	pr_rop(pr, 3, height - 2, width + 2, 2, PIX_SRC | PIX_COLOR(1), NULL, 0, 0);
	pr_rop(pr, 0, 3, 2, height - 6, PIX_SRC | PIX_COLOR(1), NULL, 0, 0);
	pr_rop(pr, width + 6, 3, 2, height - 6, PIX_SRC | PIX_COLOR(1), NULL, 0, 0);
	pr_rop(pr, 1, 1, 3, 3, PIX_SRC | PIX_DST, &tt_better_button_cross, 0, 0);
	pr_rop(pr, width + 4, 1, 3, 3, PIX_SRC | PIX_DST, &tt_better_button_cross, 0, 0);
	pr_rop(pr, width + 4, height - 4, 3, 3, PIX_SRC | PIX_DST, &tt_better_button_cross, 0, 0);
	pr_rop(pr, 1, height - 4, 3, 3, PIX_SRC | PIX_DST, &tt_better_button_cross, 0, 0);
	pos.pr = pr;
	pos.pos.x = 4 + (width - true_width) / 2;
	pos.pos.y = 4 + baseline_of(font);
	pf_ttext(pos, PIX_SRC | PIX_COLOR(1), font, text);
	return(pr);
}

/************************************************************************/
PRIVATE	image_box(gadget)

g_ptr	gadget;

{	int	w, h, mw, mh;
	cv_ptr	cv;
	double	log10();

	if (gadget->kind == GADGET_BUTTON) {
	   if (gadget->u.but.label[0]->is_icon) {
	      gadget->image = gadget->u.but.label[0]->image;
	      gadget->width = gadget->image->pr_width;
	      gadget->height = gadget->image->pr_height;
	      }
	   else {
	      gadget->width = text_width(gadget->u.but.label[0]->label, gadget->u.but.label[0]->font) + 8;
	      gadget->height = charheight_of(gadget->u.but.label[0]->font) + 6;
	      }
	   }
	else if (gadget->kind == GADGET_MENU) {
	   if (gadget->u.men.label->is_icon) {
	      gadget->image = gadget->u.men.label->image;
	      gadget->width = gadget->image->pr_width;
	      gadget->height = gadget->image->pr_height;
	      }
	   else {
	      gadget->width = text_width(gadget->u.men.label->label, gadget->u.men.label->font) + 21;
	      gadget->height = charheight_of(gadget->u.men.label->font) + 6;
	      }
	   }
	else if (gadget->kind == GADGET_LABEL) {
	   tt_construct_label(gadget->u.lab.label);
	   gadget->image = gadget->u.lab.label->image;
	   gadget->width = gadget->image->pr_width;
	   gadget->height = gadget->image->pr_height;
	   }
	else if (gadget->kind == GADGET_CHOICE) {
	   if (gadget->u.cho.label == NULL) {
	      gadget->width = -4; /* hack: correct for 4 pixel offset below */
	      gadget->height = 0;
	      }
	   else {
	      tt_construct_label(gadget->u.cho.label);
	      gadget->image = gadget->u.cho.label->image;
	      gadget->width = gadget->u.cho.label->image->pr_width;
	      gadget->height = gadget->u.cho.label->image->pr_height;
	      }
	   tt_construct_label(gadget->u.cho.mark);
	   tt_construct_label(gadget->u.cho.nomark);
	   mw = max(gadget->u.cho.mark->image->pr_width, gadget->u.cho.nomark->image->pr_width);
	   mh = max(gadget->u.cho.mark->image->pr_height, gadget->u.cho.nomark->image->pr_height);
	   for (w = h = 0, cv = gadget->u.cho.value; cv; cv = cv->next) {
	      tt_construct_label(cv->label);
	      switch (gadget->u.cho.mode) {
	         case CHOICE_CURRENT    : 
	         case CHOICE_CYCLE      : h = max(cv->label->image->pr_height, h);
				          w = max(cv->label->image->pr_width, w);
				          break;
	         case CHOICE_VERTICAL   : h += max(cv->label->image->pr_height, mh) + 4;
				          w = max(cv->label->image->pr_width, w);
				          break;
	         case CHOICE_HORIZONTAL : h = max(cv->label->image->pr_height, h);
				          w += cv->label->image->pr_width + mw + 8;
				          break;
		 }
	      }
	   switch (gadget->u.cho.mode) {
	      case CHOICE_CURRENT    : gadget->width += w + 4;
	      			       gadget->height = max(gadget->height, h);
				       break;
	      case CHOICE_CYCLE      : gadget->width += w + mw + 8;
	      			       gadget->height = max(gadget->height, h);
	      			       gadget->height = max(gadget->height, mh);
				       break;
	      case CHOICE_VERTICAL   : gadget->width += w + mw + 8;
	      			       gadget->height = max(gadget->height, h - 4);
				       break;
	      case CHOICE_HORIZONTAL : gadget->width += w;
				       gadget->height = max(gadget->height, h);
				       break;
	      }
	   gadget->u.cho.ch_width = w;
	   gadget->u.cho.ch_height = h;
	   }
	else if (gadget->kind == GADGET_SLIDER) {
	   if (gadget->u.sli.label == NULL) {
	      gadget->width = -4; /* hack: correct for 4 pixel offset below */
	      gadget->height = 0;
	      }
	   else {
	      tt_construct_label(gadget->u.sli.label);
	      gadget->image = gadget->u.sli.label->image;
	      gadget->width = gadget->u.sli.label->image->pr_width;
	      gadget->height = gadget->u.sli.label->image->pr_height;
	      }
	   gadget->height = max(gadget->height, charheight_of(gadget->u.sli.font));
	   gadget->width += 10 + gadget->u.sli.width;
	   w = max(((int) log10(abs(gadget->u.sli.minimum) + 0.1)), ((int) log10(abs(gadget->u.sli.maximum) + 0.1))) + 1;
	   if (gadget->u.sli.minimum < 0 || gadget->u.sli.maximum < 0)
	      w++;
	   if (gadget->u.sli.range)
	      gadget->width += (2 * w + 2) * charwidth_of(gadget->u.sli.font);
	   if (gadget->u.sli.value)
	      gadget->width += (w + 3) * charwidth_of(gadget->u.sli.font);
	   }
	else if (gadget->kind == GADGET_TEXT) {
	   if (gadget->u.tex.label == NULL) {
	      gadget->width = -4; /* hack: correct for 4 pixel offset below */
	      gadget->height = 0;
	      }
	   else {
	      tt_construct_label(gadget->u.tex.label);
	      gadget->image = gadget->u.tex.label->image;
	      gadget->width = gadget->u.tex.label->image->pr_width;
	      gadget->height = gadget->u.tex.label->image->pr_height;
	      }
	   gadget->width += 4 + gadget->u.tex.display_len * charwidth_of(gadget->u.tex.font);
	   gadget->height = max(charheight_of(gadget->u.tex.font), gadget->height);
	   }
}

/************************************************************************/
EXPORT	tt_build_images(d)

d_ptr	d;

{	int	i, len = 0;
	g_ptr	b;
	char	*p;

	for (b = d->gadgets; b; b = b->next) {
	   image_box(b);
	   if (b->kind == GADGET_BUTTON || b->kind == GADGET_MENU)
	      len = (b->width > len)? b->width : len;
	   }
	if (d->proportional)
	   len = 0;
	for (b = d->gadgets; b; b = b->next) {
	   if (b->kind == GADGET_BUTTON) {
	      if (b->image == NULL) {
	         b->image = better_button_image(b->u.but.label[0]->label, 0, len - 8, b->u.but.label[0]->font);
	         b->width = b->image->pr_width;
	         b->height = b->image->pr_height;
	         }
	      b->u.but.menu = menu_create(0);
	      for (i = 0; i < MAX_SHIFT_SETS; i++)
	         if (b->u.but.label[i])
	            if (b->u.but.label[i]->is_icon) {
	               menu_set(b->u.but.menu,
	               		   MENU_APPEND_ITEM, menu_create_item(MENU_IMAGE_ITEM, b->u.but.label[i]->image, b->u.but.action[i],
	               		   				      0),
	               		0);
	               }
	            else {
	               p = (char *) safe_malloc(strlen(b->u.but.label[i]->label) + 5);
	               strcpy(p, "    ");
	               strcat(p, b->u.but.label[i]->label);
	               if (i & S_SHIFT)
	                  p[0] = 'S';
	               if (i & S_CONTROL)
	                  p[1] = 'C';
	               if (i & S_META)
	                  p[2] = 'M';
	               menu_set(b->u.but.menu,
	               		   MENU_APPEND_ITEM, menu_create_item(MENU_STRING_ITEM, p, b->u.but.action[i],
	               						      MENU_FONT, b->u.but.label[i]->font,
	               						      0),
	               		0);
	               }
	      }
	   else if (b->kind == GADGET_MENU) {
	      if (b->image == NULL) {
	         b->image = better_menu_image(b->u.men.label->label, 0, len - 8, d->g_font);
	         b->width = b->image->pr_width;
	         b->height = b->image->pr_height;
	         }
	      }
	   else if (b->kind == GADGET_LABEL) {
	      /* do nothing, image_box took care of it */
	      }
	   else if (b->kind == GADGET_TEXT) {
	      /* do nothing, image_box took care of it */
	      }
	   else if (b->kind == GADGET_CHOICE) {
	      /* do nothing, image_box took care of it */
	      }
	   else if (b->kind == GADGET_SLIDER) {
	      /* do nothing, image_box took care of it */
	      }
	   }
}

/************************************************************************/
EXPORT	tt_make_gadget(d, gadget, x, y)

d_ptr	d;
g_ptr	gadget;
int	x;
int	y;

{	char	*s;
	int	i, lx, ly, mx, my, vx, vy, max_h, max_mh, max_mw;
	Panel_item	p;
	cv_ptr	cv;

	if (gadget->x != -1) {
	   x = gadget->x;
	   y = gadget->y;
	   }
	if (gadget->kind == GADGET_BUTTON || gadget->kind == GADGET_MENU)
	   p = panel_create_item(d->panel, (gadget->kind == GADGET_BUTTON)? PANEL_BUTTON : PANEL_MESSAGE,
				    PANEL_LABEL_IMAGE, gadget->image,
				    PANEL_ITEM_X, x,
				    PANEL_ITEM_Y, y,
				    PANEL_CLIENT_DATA, gadget,
				    PANEL_EVENT_PROC, event_proc,
				    PANEL_NOTIFY_PROC, notify_proc,
				    PANEL_ACCEPT_KEYSTROKE, !d->text_items_exist,
				 0);
	else if (gadget->kind == GADGET_LABEL)
	   p = panel_create_item(d->panel, PANEL_MESSAGE,
				    PANEL_LABEL_IMAGE, gadget->image,
				    PANEL_ITEM_X, x,
				    PANEL_ITEM_Y, y,
				    PANEL_CLIENT_DATA, gadget,
				    PANEL_EVENT_PROC, event_proc,
				    PANEL_NOTIFY_PROC, notify_proc,
				    PANEL_ACCEPT_KEYSTROKE, !d->text_items_exist,
				 0);
	else if (gadget->kind == GADGET_SLIDER) {
	   if (gadget->u.sli.label == NULL)
	      /* do nothing */ ;
	   else if (gadget->u.sli.label->image->pr_height > charheight_of(gadget->u.sli.font)) {
	      ly = y;
	      vy = y + (gadget->u.sli.label->image->pr_height - charheight_of(gadget->u.sli.font)) / 2;
	      }
	   else {
	      ly = y + (charheight_of(gadget->u.sli.font) - gadget->u.sli.label->image->pr_height) / 2;
	      vy = y;
	      }
	   if (gadget->u.sli.label)
	      p = panel_create_item(d->panel, PANEL_SLIDER,
	      			       PANEL_LABEL_IMAGE, gadget->image,
	      			       PANEL_LABEL_X, x,
	      			       PANEL_LABEL_Y, ly,
	      			       PANEL_VALUE_X, x + gadget->image->pr_width + 4,
	      			       PANEL_VALUE_Y, vy,
	      			    0);
	   else
	      p = panel_create_item(d->panel, PANEL_SLIDER,
	      			       PANEL_VALUE_X, x,
	      			       PANEL_VALUE_Y, y,
	      			    0);
	   panel_set(p, PANEL_MIN_VALUE, gadget->u.sli.minimum,
	   	        PANEL_MAX_VALUE, gadget->u.sli.maximum,
	   	        PANEL_VALUE, gadget->u.sli.initial,
	   	        PANEL_VALUE_FONT, gadget->u.sli.font,
	   	        PANEL_SHOW_RANGE, gadget->u.sli.range,
	   	        PANEL_SHOW_VALUE, gadget->u.sli.value,
	   	        PANEL_SLIDER_WIDTH, gadget->u.sli.width,
	   	        PANEL_CLIENT_DATA, gadget,
		        PANEL_EVENT_PROC, event_proc,
		        PANEL_NOTIFY_PROC, notify_proc,
		        PANEL_ACCEPT_KEYSTROKE, !d->text_items_exist,
		     0);
	   }
	else if (gadget->kind == GADGET_CHOICE) {
	   p = panel_create_item(d->panel, PANEL_CHOICE,
	   			    PANEL_MARK_IMAGES, gadget->u.cho.mark->image, 0,
	      		   	    PANEL_NOMARK_IMAGES, gadget->u.cho.nomark->image, 0,
	      		   	    PANEL_CLIENT_DATA, gadget,
	      		   	    PANEL_EVENT_PROC, event_proc,
	      		   	    PANEL_NOTIFY_PROC, notify_proc,
	      		   	    PANEL_FEEDBACK, (gadget->u.cho.mode != CHOICE_CURRENT)? PANEL_MARKED : PANEL_NONE,
	      		   	 0);
	   if (gadget->u.cho.mode == CHOICE_CURRENT || gadget->u.cho.mode == CHOICE_CYCLE)
	      panel_set(p, PANEL_DISPLAY_LEVEL, PANEL_CURRENT, 0);
	   else
	      panel_set(p, PANEL_DISPLAY_LEVEL, PANEL_ALL, 0);
	   max_mw = (gadget->u.cho.mode != CHOICE_CURRENT)? max(gadget->u.cho.mark->image->pr_width, gadget->u.cho.nomark->image->pr_width) : -4;
	   max_mh = (gadget->u.cho.mode != CHOICE_CURRENT)? max(gadget->u.cho.mark->image->pr_height, gadget->u.cho.nomark->image->pr_height) : 0;
	   if (gadget->u.cho.label) {
	      lx = x;
	      mx = x + gadget->u.cho.label->image->pr_width + 4;
	      vx = mx + max_mw + 4;
	      if (gadget->u.cho.label->image->pr_height > max_mh)
	         if (gadget->u.cho.label->image->pr_height > gadget->u.cho.ch_height)
	            max_h = gadget->u.cho.label->image->pr_height;
	         else
	            max_h = gadget->u.cho.ch_height;
	      else if (max_mh > gadget->u.cho.ch_height)
	         max_h = max_mh;
	      else
	         max_h = gadget->u.cho.ch_height;
	      ly = y + (max_h - gadget->u.cho.label->image->pr_height) / 2;
	      my = y + (max_h - max_mh) / 2;
	      vy = y + (max_h - gadget->u.cho.ch_height) / 2;
	      }
	   else {
	      mx = x;
	      vx = x + max_mw + 4;
	      max_h = max(max_mh, gadget->u.cho.ch_height);
	      my = y + (max_h - max_mh) / 2;
	      vy = y + (max_h - gadget->u.cho.ch_height) / 2;
	      }
	   if (gadget->u.cho.mode == CHOICE_VERTICAL) {
	      ly = y;
	      for (i = 0, vy = y, cv = gadget->u.cho.value; cv; i++, cv = cv->next) {
	         if (max_mh > cv->label->image->pr_height)
	            panel_set(p, PANEL_CHOICE_IMAGE, i, cv->label->image,
	            		 PANEL_CHOICE_X, i, vx,
	            		 PANEL_CHOICE_Y, i, vy + (max_mh - cv->label->image->pr_height) / 2,
	            		 PANEL_MARK_X, i, mx,
	            		 PANEL_MARK_Y, i, vy,
	            	      0);
	         else
	            panel_set(p, PANEL_CHOICE_IMAGE, i, cv->label->image,
	            		 PANEL_CHOICE_X, i, vx,
	            		 PANEL_CHOICE_Y, i, vy,
	            		 PANEL_MARK_X, i, mx,
	            		 PANEL_MARK_Y, i, vy + (cv->label->image->pr_height - max_mh) / 2,
	            	      0);
	         vy += max(max_mh, cv->label->image->pr_height) + 4;
	         }
	      }
	   else {
	      for (i = 0, cv = gadget->u.cho.value; cv; cv = cv->next, i++) {
	         panel_set(p, PANEL_CHOICE_IMAGE, i, cv->label->image,
	            	      PANEL_CHOICE_X, i, vx,
	            	      PANEL_CHOICE_Y, i, vy + (gadget->u.cho.ch_height - cv->label->image->pr_height) / 2,
	            	   0);
	         if (gadget->u.cho.mode != CHOICE_CURRENT)
	            panel_set(p, PANEL_MARK_X, i, mx,
	            	         PANEL_MARK_Y, i, my,
	            	      0);
	         if (gadget->u.cho.mode == CHOICE_HORIZONTAL) {
	            mx += max_mw + cv->label->image->pr_width + 8;
	            vx += max_mw + cv->label->image->pr_width + 8;
	            }
	         }
	      }
	   if (gadget->u.cho.label)
	      panel_set(p, PANEL_LABEL_IMAGE, gadget->u.cho.label->image,
	      		   PANEL_LABEL_X, lx,
	      		   PANEL_LABEL_Y, ly,
	      		0);
	   }
	else if (gadget->kind == GADGET_TEXT) {
	   if (gadget->u.tex.label == NULL)
	      vy = y;
	   else if (gadget->u.tex.label->is_icon)
	      if (gadget->u.tex.label->image->pr_height > gadget->u.tex.font->pf_defaultsize.y) {
	         ly = y;
	         vy = y + (gadget->height - gadget->u.tex.font->pf_defaultsize.y) / 2;
	         }
	      else {
	         ly = y + (gadget->height - gadget->u.tex.label->image->pr_height) / 2;
	         vy = y;
	         }
	   else
	      if (gadget->u.tex.label->font->pf_defaultsize.y > gadget->u.tex.font->pf_defaultsize.y) {
	         ly = y;
	         vy = y + (baseline_of(gadget->u.tex.label->font) - baseline_of(gadget->u.tex.font));
	         }
	      else {
	         ly = y + (baseline_of(gadget->u.tex.font) - baseline_of(gadget->u.tex.label->font));
	         vy = y;
	         }
	   if (gadget->u.tex.label)
	      p = panel_create_item(d->panel, PANEL_TEXT,
	      			       PANEL_LABEL_IMAGE, gadget->image,
	      			       PANEL_LABEL_X, x,
	   	     		       PANEL_LABEL_Y, ly,
	      			    0);
	   else
	      p = panel_create_item(d->panel, PANEL_TEXT, 0);
	   panel_set(p, PANEL_VALUE_X, gadget->u.tex.label? x + 4 + gadget->image->pr_width : x,
		        PANEL_VALUE_Y, vy,
		        PANEL_VALUE_DISPLAY_LENGTH, gadget->u.tex.display_len,
		        PANEL_VALUE_STORED_LENGTH, gadget->u.tex.retain_len,
		        PANEL_VALUE_FONT, gadget->u.tex.font,
	   		PANEL_NOTIFY_LEVEL, PANEL_ALL,
	   		PANEL_CLIENT_DATA, gadget,
	   		PANEL_EVENT_PROC, event_proc,
	   		PANEL_NOTIFY_PROC, notify_proc,
	   	     0);
	   }
	gadget->panel_item = p;
}
