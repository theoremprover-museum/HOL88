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

#define		RETURN(x)		return(last_token = (x))

#define		FIRST_KEYWORD		ACTION
#define		LAST_KEYWORD		WIDTH
#define		NUM_KEYWORDS		(LAST_KEYWORD - FIRST_KEYWORD + 1)

#define		CPP			"/lib/cpp"

PRIVATE	FILE	*f;
PRIVATE	int	last_token = -1;
PRIVATE	char	buf[1024];

PRIVATE	struct	{char	*name;
		 int	value;
		} token[] = {{"action",		ACTION},
			     {"align",		ALIGN},
			     {"application",	APPLICATION},
			     {"at",		AT},
			     {"base",		BASE},
			     {"beep",		BEEP},
			     {"bottom",		BOTTOM},
			     {"break",		BREAK},
			     {"button",		BUTTON},
			     {"by",		BY},
			     {"center",		CENTER},
			     {"characters",	CHARACTERS},
			     {"choice",		CHOICE},
			     {"close",		CLOSE},
			     {"completion",	COMPLETION},
			     {"continue",	CONTINUE},
			     {"control",	CONTROL},
			     {"current",	CURRENT},
			     {"cycle",		CYCLE},
			     {"dialog",		DIALOG},
			     {"disable",	DISABLE},
			     {"display",	DISPLAY},
			     {"else",		ELSE},
			     {"end_button",	END_BUTTON},
			     {"end_choice",	END_CHOICE},
			     {"end_dialog",	END_DIALOG},
			     {"end_gadgets",	END_GADGETS},
			     {"end_key",	END_KEY},
			     {"end_keys",	END_KEYS},
			     {"end_label",	END_LABEL},
			     {"end_menu",	END_MENU},
			     {"end_mouse",	END_MOUSE},
			     {"end_slider",	END_SLIDER},
			     {"end_text",	END_TEXT},
			     {"exit",		EXIT},
			     {"font",		FONT},
			     {"for",		FOR},
			     {"function_keys",	FUNCTION_KEYS},
			     {"gadgets",	GADGETS},
			     {"horizontal",	HORIZONTAL},
			     {"icon",		ICON},
			     {"if",		IF},
			     {"ignore",		IGNORE},
			     {"initial",	INITIAL},
			     {"initialize",	INITIALIZE},
			     {"key",		KEY},
			     {"keys",		KEYS},
			     {"label",		LABEL},
			     {"left",		LEFT},
			     {"mark",		MARK},
			     {"maximum",	MAXIMUM},
			     {"menu",		MENU},
			     {"meta",		META},
			     {"middle",		MIDDLE},
			     {"minimum",	MINIMUM},
			     {"mouse",		MOUSE},
			     {"nomark",		NOMARK},
			     {"normal",		NORMAL},
			     {"normal_keys",	NORMAL_KEYS},
			     {"nothing",	NOTHING},
			     {"off",		OFF},
			     {"on",		ON},
			     {"open",		OPEN},
			     {"pixels",		PIXELS},
			     {"popup",		POPUP},
			     {"proportional",	PROPORTIONAL},
			     {"ragged",		RAGGED},
			     {"range",		RANGE},
			     {"remove",		REMOVE},
			     {"retain",		RETAIN},
			     {"right",		RIGHT},
			     {"send",		SEND},
			     {"shift",		SHIFT},
			     {"size",		SIZE},
			     {"slider",		SLIDER},
			     {"text",		TEXT},
			     {"timer",		TIMER},
			     {"top",		TOP},
			     {"trigger",	TRIGGER},
			     {"ttymenu",	TTYMENU},
			     {"value",		VALUE},
			     {"vertical",	VERTICAL},
			     {"while",		WHILE},
			     {"width",		WIDTH}};

PRIVATE	struct	{char	first;
		 char	next;
		 int	name;
		} punc[] = {{'&',  '\0', LOGICAL_AND},
			    {'&',  '&',  AND},
			    {'&',  '=',  ASSIGN_AND},
			    {':',  '\0', COLON},
			    {',',  '\0', COMMA},
			    {'~',  '\0', COMPLEMENT},
			    {'=',  '\0', ASSIGNMENT},
			    {'=',  '=',  EQUAL},
			    {'>',  '\0', GREATER},
			    {'>',  '=',  GREATER_EQUAL},
			    {'>',  '>',  RIGHT_SHIFT},
			    {'{',  '\0', LBRACE},
			    {'[',  '\0', LBRACK},
			    {'<',  '\0', LESS},
			    {'<',  '=',  LESS_EQUAL},
			    {'<',  '<',  LEFT_SHIFT},
			    {'!',  '\0', LOGICAL_NOT},
			    {'!',  '=',  NOT_EQUAL},
			    {'|',  '\0', OR},
			    {'|',  '|',  LOGICAL_OR},
			    {'|',  '=',  ASSIGN_OR},
			    {'(',  '\0', LPAREN},
			    {'-',  '\0', MINUS},
			    {'-',  '-',  DECREMENT},
			    {'-',  '=',  ASSIGN_MINUS},
			    {'%',  '\0', MODULO},
			    {'%',  '=',  ASSIGN_MODULO},
			    {'+',  '\0', PLUS},
			    {'+',  '+',  INCREMENT},
			    {'+',  '=',  ASSIGN_PLUS},
			    {'?',  '\0', QUESTION},
			    {'}',  '\0', RBRACE},
			    {']',  '\0', RBRACK},
			    {')',  '\0', RPAREN},
			    {';',  '\0', SEMICOLON},
			    {'*',  '\0', TIMES},
			    {'*',  '=',  ASSIGN_TIMES},
			    {'^',  '\0', XOR},
			    {'^',  '=',  ASSIGN_XOR},
			    {'\0', '\0', -1}};

PRIVATE	char	getch()

{	register	char	c;
	static		int	first = TRUE;

	if (first) {
	   first = FALSE;
	   if ((f = popen(CPP, "r")) == NULL)
	      abend("could not invoke %s", CPP);
	   }
	if (ungetc != -1)
	   c = ungetc, ungetc = -1;
	else {
	   c = getc(f);
	   if (c == '\n')
	      line_count++;
	   }
	return(c);
}

PRIVATE	fix_escapes(buf)

char	*buf;

{	char	*q;
	int	i;

	for (q = buf; *buf; buf++, q++)
	   if (*buf == '\\')
	      switch (*++buf) {
	         case 'b' : *q = '\010'; /* ^h */
	            	    break;
	         case 'e' : *q = '\033'; /* esc */
	          	    break;
	         case 'f' : *q = '\014'; /* ^l */
	            	    break;
	         case 'n' : *q = '\012'; /* ^j */
	            	    break;
	         case 'r' : *q = '\015'; /* ^m */
	            	    break;
	         case 't' : *q = '\011'; /* ^i */
	            	    break;
	         case '0' : 
	         case '1' : 
	         case '2' : 
	         case '3' : 
	         case '4' : 
	         case '5' : 
	         case '6' : 
	         case '7' : *q = *buf++ - '0';
	            	    for (i = 0; i < 2 && *buf >= '0' && *buf <= '7'; i++)
	            	       *q = (*q << 3) + *buf++ - '0';
	            	    buf--;
	            	    break;
	         default  : *q = *buf;
	            	    break;
	         }
	   else if (*buf == '^' && *(buf + 1) >= '@' && *(buf + 1) <= '_')
	      *q = *++buf & 0x1f;
	   else
	      *q = *buf;
	*q = '\0';
}

PRIVATE	int	is_keyword(s)

char	*s;

{	register	int	cmp, high, low, pos;

	for (low = 0, high = NUM_KEYWORDS - 1; low <= high; )
	   if ((cmp = strcmp(s, token[pos = (high - low) / 2 + low].name)) == 0)
	      return(token[pos].value);
	   else if (cmp < 0)
	      high = pos - 1;
	   else
	      low = pos + 1;
	return(NULL);
}

PRIVATE	int	yylex()

{	register	char	c, c1, *p;
	register	int	i, j, val;
	char			*index();
	double			atof();

	c = getch();
	while (isspace(c))
	   c = getch();
	if (isalpha(c)) {
	   p = buf;
	   *p++ = c;
	   while (isalnum(c = getch()) || c == '_')
	      *p++ = c;
	   ungetc = c;
	   *p = '\0';
	   for (p = buf; *p; p++)
	      if (isupper(*p))
	         *p = tolower(*p);
	   if (i = is_keyword(buf))
	      RETURN(i);
	   if ((i = strlen(buf)) == 2) { /* possible two character function key name */
	      if (buf[0] == 'l' && buf[1] >= '2' && buf[1] <= '9') /* l2 - l9 */
	         RETURN(yylval.ival = L2 + buf[1] - '2');
	      else if (buf[0] == 'f' && buf[1] >= '1' && buf[1] <= '9') /* f1 - f9 */
	         RETURN(yylval.ival = F1 + buf[1] - '1');
	      else if (buf[0] == 'r' && buf[1] >= '1' && buf[1] <= '9') /* r1 - r9 */
	         RETURN(yylval.ival = R1 + buf[1] - '1');
	      }
	   else if (i == 3) { /* possible three character function key name */
	      if (buf[0] == 'l' && buf[1] == '1' && buf[2] == '0')
	         RETURN(yylval.ival = L10);
	      else if (buf[0] == 'r' && buf[1] == '1' && buf[2] >= '0' && buf[2] <= '5') /* r10 - r15 */
	         RETURN(yylval.ival = R10 + buf[2] - '0');
	      }
	   fix_escapes(buf);
	   yylval.cpval = strsave(buf);
	   RETURN(ID);
	   }
	else if (c == '"') {
	   for (p = buf; TRUE; p++)
	      if ((*p = getch()) == '"')
	         break;
	      else if (*p == '\\')
	         *++p = getch();
	      else if (*p == '\n' || *p == '\r') {
	         yyerror("Newline in string not allowed");
	         break;
	         }
	   *p = '\0';
	   fix_escapes(buf);
	   yylval.cpval = strsave(buf);
	   RETURN(STRING);
	   }
	else if (c == '\'') {
	   p = buf;
	   for (p = buf; TRUE; p++)
	      if ((*p = getch()) == '\'')
	         break;
	      else if (*p == '\\')
	         *++p = getch();
	      else if (*p == '\n' || *p == '\r') {
	         yyerror("Newline in string not allowed");
	         break;
	         }
	   *p = '\0';
	   fix_escapes(buf);
	   yylval.cpval = strsave(buf);
	   RETURN(ICON_STRING);
	   }
	else if (isdigit(c)) {
	   if (c == '0') {
	      if ((c = getch()) == 'x') /* hex number */
	         for (val = 0; isxdigit(c = getch()); )
	            if (isdigit(c))
	               val = val * 16 + c - '0';
	            else
	               val = val * 16 + c - (isupper(c)? 'A' : 'a');
	      else if (isdigit(c)) /* octal */
	         for (val = c - '0'; (c = getch()) >= '0' && c <= '7'; )
	            val = val * 8 + c - '0';
	      else if (c == '.') {
	         ungetc = c;
	         c = '0';
	         goto do_real; /* with God as my witness, I'll never do this again, I swear */
	         }
	      else
	         val = 0;
	      ungetc = c;
	      yylval.ival = val;
	      RETURN(INTEGER);
	      }
	   else {
do_real:      p = buf;
	      *p++ = c;
	      val = INTEGER;
	      while (isdigit(c = getch()))
	         *p++ = c;
	      if (c == '.')
	         for (*p++ = c, val = REAL; isdigit(c = getch()); )
	            *p++ = c;
	      if (c == 'e' || c == 'E') {
	         *p++ = c;
	         if ((c = getch()) == '-' || c == '+')
	            *p++ = c;
	         else
	            ungetc = c;
	         for (val = REAL; isdigit(c = getch()); )
	            *p++ = c;
	         }
	      *p = '\0';
	      ungetc = c;
	      if (val == INTEGER)
	         yylval.ival = atoi(buf);
	      else
	         yylval.rval = atof(buf);
	      RETURN(val);
	      }
	   }
	else if (c == '/') {
	   if ((c = getch()) == '*') {
	      while (1) {
	         while ((c = getch()) != '*')
	            ;
	         if ((c = getch()) == '/')
	            break;
	         }
	      }
	   else if (c == '=')
	      RETURN(ASSIGN_DIVIDE);
	   else {
	      ungetc = c;
	      RETURN(DIVIDE);
	      }
	   }
	else if (c == '#') {
	   if (yylex() == INTEGER) {
	      line_count = yylval.ival - 1; /* getch will bump by 1 when \n is read */
	      if (yylex() == STRING) {
	         if (*yylval.cpval)
	            tt_curr_file = yylval.cpval;
	         while (getch() != '\n')
	            ;
	         RETURN(yylex());
	         }
	      }
	   yyerror("Invalid cpp control sequence in source file");
	   }
	else if (c == EOF) {
	   pclose(f);
	   RETURN(EOF);
	   }
	else {
	   for (i = 0; punc[i].first; i++)
	      if (c == punc[i].first) {
	         for (c1 = getch(), j = 1; punc[i + j].first == c; j++)
	            if (c1 == punc[i + j].next)
	               RETURN(punc[i + j].name);
	         ungetc = c1;
	         RETURN(punc[i].name);
	         }
	   yyerror("Invalid character in source file: %c (0x%02x)", c, c);
	   }
	RETURN(yylex());
}

/************************************************************************/
PRIVATE	print_last_token()

{	int	i;

	fprintf(stderr, " at or near \"");
	if (last_token == INTEGER || last_token == REAL || last_token == STRING || last_token == ICON_STRING || last_token == ID)
	   fprintf(stderr, buf);
	else if (last_token >= L2 && last_token <= L10)
	   fprintf(stderr, "L%d", last_token - L2 + 2);
	else if (last_token >= F1 && last_token <= F9)
	   fprintf(stderr, "F%d", last_token - F1 + 1);
	else if (last_token >= R1 && last_token <= R15)
	   fprintf(stderr, "R%d", last_token - R1 + 1);
	else if (last_token >= AND && last_token <= XOR) {
	   for (i = 0; punc[i].first; i++)
	      if (punc[i].name == last_token) {
	         fprintf(stderr, "%c", punc[i].first);
	         if (punc[i].next)
	            fprintf(stderr, "%c", punc[i].next);
	         break;
	         }
	   if (punc[i].first == '\0')
	      fprintf(stderr, "!!Geez!  Some punctuation, I don't know!!");
	   }
	else if (last_token >= FIRST_KEYWORD && last_token <= LAST_KEYWORD)
	   fprintf(stderr, token[last_token - FIRST_KEYWORD].name);
	else if (last_token == EOF)
	   fprintf(stderr, "End Of File");
	else
	   fprintf(stderr, "!!Geez!  Some keyword, I don't know!!");
	fprintf(stderr, "\"");
}
