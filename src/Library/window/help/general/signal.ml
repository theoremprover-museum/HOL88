\DOC signal

\TYPE {signal : (* signal -> * -> void)}

\SYNOPSIS
Raises a signal.

\LIBRARY windows

\DESCRIBE
{signal s a} evaluates for their side effects all the signal handler functions 
that have been associate with the signal {s}.
Each of the signal handler functions is invoked with the argument {a}.

\FAILURE
Never fails.

\SEEALSO
clear, handle, sigtype.

\ENDDOC
