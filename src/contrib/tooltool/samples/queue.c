#include	<stdio.h>
#include	<signal.h>
#include	<sgtty.h>
#include	<sys/time.h>
#include	<pwd.h>

#define		strsave(s)	((char *) strcpy((char *) malloc(strlen(s) + 1), s))

#define		CLEAR		"\014"
#define		BOLD_ON		"\033[7m"
#define		BOLD_OFF	"\033[m"

#define		LPQ		"/usr/ucb/lpq"

struct	itimerval	interval = {{10, 0}, {10, 0}};
struct	itimerval	zero_timer = {{0, 0}, {0, 0}};

char	*user_name;

char	*strindex(source, target)

char	*source;
char	*target;

{	register	int	len;

	len = strlen(target);
	for (; *source; source++)
	   if (strncmp(source, target, len) == 0)
	      return(source);
	return(0);
}

poll()

{	FILE	*f;
	char	buf[256];
	int	line;

	if ((f = popen(LPQ, "r")) == NULL) {
	   printf("%s%sCould not execute %s%s\n", CLEAR, BOLD_ON, LPQ, BOLD_OFF);
	   return;
	   }
	printf(CLEAR);
	for (line = 1; fgets(buf, 256, f) != NULL; line++)
	   if (line <= 2 || strindex(buf, user_name))
	      printf("%s%s%s", BOLD_ON, buf, BOLD_OFF);
	   else
	      printf(buf);
	pclose(f);
}

start_timer()

{
	setitimer(ITIMER_REAL, &interval, NULL);
}

stop_timer()

{
	setitimer(ITIMER_REAL, &zero_timer, NULL);
}

main()

{	char	c;
	int	i;
	struct	sgttyb	tty, old_in, old_out;
	struct	passwd	*pp;

	pp = getpwuid(getuid());
	user_name = strsave(pp->pw_name);

	ioctl(0, TIOCGETP, &old_in);
	tty = old_in;
	tty.sg_flags |= CBREAK;
	tty.sg_flags &= ~ECHO;
	ioctl(0, TIOCSETP, &tty);

	ioctl(1, TIOCGETP, &old_out);
	tty = old_out;
	tty.sg_flags |= CBREAK;
	tty.sg_flags &= ~ECHO;
	ioctl(1, TIOCSETP, &tty);

	signal(SIGALRM, poll);
	poll();
	start_timer();
	while ((c = getchar()) != EOF)
	   switch (c) {
	      case 'b' : start_timer();
	      		 while (getchar() != '\n')
	      		    ;
	      		 break;
	      case 'e' : stop_timer();
	      		 while (getchar() != '\n')
	      		    ;
	      		 break;
	      case 'i' : for (i = 0; (c = getchar()) != '\n'; )
	      		    if (c >= '0' && c <= '9')
	      		       i = i * 10 + c - '0';
	      		 if (i == 0)
	      		    break;
	      		 interval.it_value.tv_sec = i;
	      		 interval.it_value.tv_usec = 0;
	      		 interval.it_interval.tv_sec = i;
	      		 interval.it_interval.tv_usec = 0;
	      		 start_timer();
	      		 break;
	      case 'q' : stop_timer();
			 ioctl(0, TIOCSETP, &old_in);
			 ioctl(1, TIOCSETP, &old_out);
	      		 exit(0);
	      }
	ioctl(0, TIOCSETP, &old_in);
	ioctl(1, TIOCSETP, &old_out);
	exit(0);
}
