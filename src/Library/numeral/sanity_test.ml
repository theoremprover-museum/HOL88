%
-------------------------------------------------------------------------------
sanity_test :
   ((* -> **) ->
   string ->
   (* -> ** -> *** -> bool) ->
   (string # * # (*** + string)) list ->
   string)

Synopsis:

Test a function to ensure that it returns the expected values.

Description:

Its inputs are:
  f             a function to test
  f_name        the name of that function as a string
  relation      a function that compares the input, the actual output, and
                the expected output and returns true if the actual output
                was correct
  test_cases    a list of triples, each of which is a test case, consisting
                of a string that identifies the test case and is to be printed
                out in case of failure, an input, and an expected output.
                The expected output is a value or a failure string.
If all test cases pass, a string is printed saying so.  If any test case
fails, a list is printed of the identification strings of all failing test
cases, and then the whole function fails.

Failure:

If any test case fails.

Examples:

#let ten_div_by x = 10/x;;
ten_div_by = - : (int -> int)
Run time: 0.0s

#sanity_test ten_div_by `ten_div_by`
  (\ input actual expected. actual = expected)
  let returns, failswith = inl, inr in [
`test 1: zero`,
        0,      failswith `div`;
`test 2: one`,
        1,      returns 10;
`test 3: a relatively small number`,
        5,      returns 2;
`test 4: a negative number`,
        -2,     returns (-5);
`test 5: a large number`,
        999999, returns 0 ];;
#############`Successful sanity test of ten_div_by` : string
Run time: 0.0s

#sanity_test ten_div_by `ten_div_by`
  (\ input actual expected. actual = expected)
  let returns, failswith = inl, inr in [
`test 6: purposely err by predicting a failure that won't appear`,
        -2,     failswith `foo`;
`test 7: purposely err by not predicting a failure`,
        0,      returns (-5);
`test 8: purposely err by predicting the wrong answer`,
        -2,     returns (-4) ];;

#########
Failures testing ten_div_by --
  test 6: purposely err by predicting a failure that won't appear
  test 7: purposely err by not predicting a failure
  test 8: purposely err by predicting the wrong answer
evaluation failed     sanity test

Revision history (most recent first):

  Fall 1993             Tim Leonard

  Test a user-supplied function on a list of user-supplied test cases.
  Use a user-supplied arbitrary relation to compare actual to expected output.
  Support testing that functions fail as they're supposed to.
  Print a user-supplied description of each case in which the function errs.
  Return a success string if the function never errs, and otherwise fail.
-------------------------------------------------------------------------------
%

%
A sanity test of a function tries the function on a list of test cases to see
if the results are what is expected.  If they are, it prints a message saying
the test was successful.  If they are not, it prints the description of each
test case that fails, and then it fails.
%

let sanity_test function function_name relation test_cases =
  %
  Define a predicate that is true if the function produces the correct result
  and false if the function produces an erroneous result.  Where the function
  is expected to return a value, that's easy.  We use the provided relation
  to compare the function's output with the expected output, and the relation
  returns the value we want.  If the function fails, we return false.  Where
  the function is supposed to fail, though, we must verify that it fails, and
  that it fails with the correct failure string.
  %
  let result_is_correct (description, input, expected_output) =
    if (isl expected_output) then
      ((relation input (function input) (outl expected_output)) ? false)
    else
      (((function input; false) ?? [outr expected_output] true) ? false)
    in
  %
  Get the list of descriptions of the testcases that failed their tests.
  %
  let failure_description (description, input, expected_output) =
    if result_is_correct (description, input, expected_output)
      then fail else description in
  let failure_strings = mapfilter failure_description test_cases in
    if failure_strings = [] then
      `Successful sanity test of ` ^ function_name
    else
    ( print_newline ();
      print_list
      true
      (`Failures testing `^function_name)
      print_string
      (rev failure_strings);
      failwith `sanity test` );;

sanity_test (sanity_test (\x.10/x) `a function that's supposed to fail` (\in act exp.act=exp)) `sanity_test`
  (\input actual expected. actual = expected)
  let returns, failswith = inl, inr in [
`test 1: correct results produce success message`,
        [`test 1.1: f returns correct result`, 1, returns 10;
         `test 1.2: f fails with correct string`, 0, failswith `div` ],
        returns `Successful sanity test of a function that's supposed to fail`;
`test 2: incorrect results produce failure`,
        [`case 1 of 4: ignore this output`, 1, returns 9;
         `case 2 of 4: ignore this output`, 1, failswith `div`;
         `case 3 of 4: ignore this output`, 0, failswith `DIV`;
         `case 3 of 4: ignore this output`, 0, returns 9 ],
        failswith `sanity test` ];;


sanity_test CONS_OF_SNOC_CONV `CONS_OF_SNOC_CONV` relation [
`test 1: a null list`,
        "[]: num list",                     returns "[]: num list";
`test 2: a one-element list`,
        "SNOC 3 []",                        returns "[3]";
`test 3: a multi-element list`,
        "SNOC 3 (SNOC 2 (SNOC 1 []))",      returns "[1;2;3]";
`test 4: a list of lists`,
        "SNOC[1;2;3](SNOC[3;4][])",         returns "CONS [3;4] (CONS [1;2;3] [])" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test SNOC_OF_CONS_CONV `SNOC_OF_CONS_CONV` relation [
`test 1: a null list`,
        "[]: num list",                         returns "[]: num list";
`test 2: a one-element list`,
        "[3]",                                  returns "SNOC 3 []";
`test 3: a multi-element list`,
        "[1;2;3]",                              returns "SNOC 3 (SNOC 2 (SNOC 1 []))";
`test 4: a list of lists`,
        "CONS [3;4] (CONS [1;2;3] [])",         returns "SNOC[1;2;3](SNOC[3;4][])" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test LENGTH_COMPARE_CONV `LENGTH_COMPARE_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) = LENGTH ([]: num list)",        returns "=: num -> num -> bool";
`test 2: length of nil less`,
        "LENGTH ([]: num list) < LENGTH [2]",                   returns "<";
`test 3: length greater than nil`,
        "LENGTH [3] > LENGTH ([]: * list)",                     returns ">";
`test 4: singletons`,
        "LENGTH [22] <= LENGTH [[0]]",                          returns "=: num -> num -> bool";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] * LENGTH [5;5;5]",                      returns "=: num -> num -> bool";
`test 6: less than longer list`,
        "LENGTH [[2]] DIV LENGTH [6;5;4;3;3]",                  returns "<";
`test 7: longer list greater than`,
        "LENGTH [1;1] MOD LENGTH [(2,3)]",                      returns ">" ]
where relation input actual expected =
  let left, right = (rand # I) (dest_comb input) in
  concl actual = mk_eq( mk_binary_comb expected left right, "T" )
and returns, failswith = inl, inr;;

sanity_test LENGTH_EQ_CONV `LENGTH_EQ_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) = LENGTH ([]: num list)",        returns "T";
`test 2: length of nil less`,
        "LENGTH ([]: num list) = LENGTH [2]",                   returns "F";
`test 3: length greater than nil`,
        "LENGTH [3] = LENGTH ([]: * list)",                     returns "F";
`test 4: singletons`,
        "LENGTH [22] = LENGTH [[0]]",                           returns "T";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] = LENGTH [5;5;5]",                      returns "T";
`test 6: less than longer list`,
        "LENGTH [[2]] = LENGTH [6;5;4;3;3]",                    returns "F";
`test 7: longer list greater than`,
        "LENGTH [1;1] = LENGTH [(2,3)]",                        returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test LENGTH_LT_CONV `LENGTH_LT_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) < LENGTH ([]: num list)",        returns "F";
`test 2: length of nil less`,
        "LENGTH ([]: num list) < LENGTH [2]",                   returns "T";
`test 3: length greater than nil`,
        "LENGTH [3] < LENGTH ([]: * list)",                     returns "F";
`test 4: singletons`,
        "LENGTH [22] < LENGTH [[0]]",                           returns "F";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] < LENGTH [5;5;5]",                      returns "F";
`test 6: less than longer list`,
        "LENGTH [[2]] < LENGTH [6;5;4;3;3]",                    returns "T";
`test 7: longer list greater than`,
        "LENGTH [1;1] < LENGTH [(2,3)]",                        returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test LENGTH_LE_CONV `LENGTH_LE_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) <= LENGTH ([]: num list)",       returns "T";
`test 2: length of nil less`,
        "LENGTH ([]: num list) <= LENGTH [2]",                  returns "T";
`test 3: length greater than nil`,
        "LENGTH [3] <= LENGTH ([]: * list)",                    returns "F";
`test 4: singletons`,
        "LENGTH [22] <= LENGTH [[0]]",                          returns "T";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] <= LENGTH [5;5;5]",                     returns "T";
`test 6: less than longer list`,
        "LENGTH [[2]] <= LENGTH [6;5;4;3;3]",                   returns "T";
`test 7: longer list greater than`,
        "LENGTH [1;1] <= LENGTH [(2,3)]",                       returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test LENGTH_GT_CONV `LENGTH_GT_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) > LENGTH ([]: num list)",        returns "F";
`test 2: length of nil less`,
        "LENGTH ([]: num list) > LENGTH [2]",                   returns "F";
`test 3: length greater than nil`,
        "LENGTH [3] > LENGTH ([]: * list)",                     returns "T";
`test 4: singletons`,
        "LENGTH [22] > LENGTH [[0]]",                           returns "F";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] > LENGTH [5;5;5]",                      returns "F";
`test 6: less than longer list`,
        "LENGTH [[2]] > LENGTH [6;5;4;3;3]",                    returns "F";
`test 7: longer list greater than`,
        "LENGTH [1;1] > LENGTH [(2,3)]",                        returns "T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test LENGTH_GE_CONV `LENGTH_GE_CONV` relation [
`test 1: nil lists`,
        "LENGTH ([]: ind list) >= LENGTH ([]: num list)",       returns "T";
`test 2: length of nil less`,
        "LENGTH ([]: num list) >= LENGTH [2]",                  returns "F";
`test 3: length greater than nil`,
        "LENGTH [3] >= LENGTH ([]: * list)",                    returns "T";
`test 4: singletons`,
        "LENGTH [22] >= LENGTH [[0]]",                          returns "T";
`test 5: equal-length longer lists`,
        "LENGTH [3;4;4] >= LENGTH [5;5;5]",                     returns "T";
`test 6: less than longer list`,
        "LENGTH [[2]] >= LENGTH [6;5;4;3;3]",                   returns "F";
`test 7: longer list greater than`,
        "LENGTH [1;1] >= LENGTH [(2,3)]",                       returns "T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test fast_num_CONV `fast_num_CONV` relation [
`test 1: smallest term`,
        "1",    returns "SUC 0";
`test 2: small term`,
        "3",    returns "SUC 2";
`test 3: small term`,
        "91",   returns "SUC 90";
`test 4: largest small term`,
        "256",  returns "SUC 255";
`test 5: smallest large term`,
        "257",  returns "SUC 256";
`test 6: large term`,
        "300",  returns "SUC 299" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test fast_GT_CONV `fast_GT_CONV` relation [
`test 1: smallest equal terms`,
        "0 > 0",        returns "F";
`test 2: smallest terms that are less`,
        "0 > 1",        returns "F";
`test 3: smallest terms that are greater`,
        "1 > 0",        returns "T";
`test 4: small terms that are greater`,
        "7 > 2",        returns "T";
`test 5: near small/large boundary`,
        "15 > 15",      returns "F";
`test 6: near small/large boundary`,
        "15 > 16",      returns "F";
`test 7: near small/large boundary`,
        "15 > 17",      returns "F";
`test 8: near small/large boundary`,
        "16 > 15",      returns "T";
`test 9: near small/large boundary`,
        "16 > 16",      returns "F";
`test 10: near small/large boundary`,
        "16 > 17",      returns "F";
`test 11: near small/large boundary`,
        "17 > 16",      returns "T";
`test 12: near small/large boundary`,
        "17 > 17",      returns "F";
`test 13: large terms that are less`,
        "21 > 24",      returns "F";
`test 13: large terms that are equal`,
        "21 > 21",      returns "F";
`test 14: large terms that are greater`,
        "24 > 21",      returns "T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test fast_LT_CONV `fast_LT_CONV` relation [
`test 1: smallest terms`,
        "0 < 0",        returns "F";
`test 2: smallest terms that are less`,
        "0 < 1",        returns "T";
`test 3: smallest terms that are greater`,
        "1 < 0",        returns "F";
`test 4: small terms that are less`,
        "3 < 11",       returns "T";
`test 5: small terms that are greater`,
        "7 < 2",        returns "F";
`test 6: near small/large boundary`,
        "15 < 15",      returns "F";
`test 7: near small/large boundary`,
        "15 < 16",      returns "T";
`test 8: near small/large boundary`,
        "15 < 17",      returns "T";
`test 9: near small/large boundary`,
        "16 < 15",      returns "F";
`test 10: near small/large boundary`,
        "16 < 16",      returns "F";
`test 11: near small/large boundary`,
        "16 < 17",      returns "T";
`test 12: near small/large boundary`,
        "17 < 16",      returns "F";
`test 13: near small/large boundary`,
        "17 < 17",      returns "F";
`test 14: near small/large boundary`,
        "17 < 19",      returns "T";
`test 15: large terms that are less`,
        "21 < 24",      returns "T";
`test 16: large terms that are equal`,
        "21 < 21",      returns "F";
`test 17: large terms that are greater`,
        "24 < 21",      returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test basen_of_int `basen_of_int` relation [
`test 1: zero`,
        (2,0),                  returns "BASEN 2[]";
`test 2: small nonzero numeral`,
        (16,8),                 returns "BASEN 16[8]";
`test 3: large nonzero numeral`,
        (10,93847),             returns "BASEN 10[9;3;8;4;7]" ]
where relation input actual expected =
  actual = expected
and returns, failswith = inl, inr;;

sanity_test int_of_basen `int_of_basen` relation [
`test 1: null numeral`,
        "BASEN 2 []",           returns 0;
`test 2: zero numeral`,
        "BASEN 9 [0]",          returns 0;
`test 3: multidigit zero numeral`,
        "BASEN 16 [0;0;0]",     returns 0;
`test 4: single-digit nonzero numeral`,
        "BASEN 13 [9]",         returns 9;
`test 5: multidigit nonzero numeral`,
        "BASEN 10 [3;9;4;5]",   returns 3945;
`test 6: large numeral with leading zeros`,
        "BASEN 16 [0;8;0;0]",   returns 2048 ]
where relation input actual expected =
  actual = expected
and returns, failswith = inl, inr;;

sanity_test IS_BASEN_CONV `IS_BASEN_CONV` relation [
`test 1: empty numeral`,
        "IS_BASEN 10 []",       returns "T";
`test 2: smallest digit`,
        "IS_BASEN 10 [0]",      returns "T";
`test 3: small decimal digit`,
        "IS_BASEN 10 [5]",      returns "T";
`test 4: largest decimal digit`,
        "IS_BASEN 10 [9]",      returns "T";
`test 5: too-large decimal digit`,
        "IS_BASEN 10 [10]",     returns "F";
`test 6: empty base-0 numeral`,
        "IS_BASEN 0 []",        returns "T";
`test 7: zero base-0 numeral`,
        "IS_BASEN 0 [0]",       returns "F";
`test 8: empty base-1 numeral`,
        "IS_BASEN 1 []",        returns "T";
`test 9: zero base-1 numeral`,
        "IS_BASEN 1 [0]",       returns "T";
`test 10: too-large base-1 digit`,
        "IS_BASEN 1 [1]",       returns "F";
`test 11: empty binary numeral`,
        "IS_BASEN 2 []",        returns "T";
`test 12: zero binary numeral`,
        "IS_BASEN 2 [0]",       returns "T";
`test 13: too-large binary digit`,
        "IS_BASEN 2 [1]",       returns "T";
`test 14: too-large binary digit`,
        "IS_BASEN 2 [5]",       returns "F";
`test 15: empty weird-base numeral`,
        "IS_BASEN 3 []",        returns "T";
`test 16: zero weird-base numeral`,
        "IS_BASEN 3 [0]",       returns "T";
`test 17: too-large weird-base digit`,
        "IS_BASEN 3 [2]",       returns "T";
`test 18: too-large weird-base digit`,
        "IS_BASEN 3 [3]",       returns "F";
`test 19: too-large weird-base digit`,
        "IS_BASEN 3 [0;0;1]",   returns "T";
`test 20: too-large weird-base digit`,
        "IS_BASEN 3 [1;2;2]",   returns "T";
`test 21: too-large weird-base digit`,
        "IS_BASEN 3 [1;3]",     returns "F";
`test 22: too-large weird-base digit`,
        "IS_BASEN 3 [3;0;2]",   returns "F";
`test 23: empty large-base numeral`,
        "IS_BASEN 23 []",       returns "T";
`test 24: zero large-base numeral`,
        "IS_BASEN 24 [0]",      returns "T";
`test 25: small large-base digit`,
        "IS_BASEN 25 [15]",     returns "T";
`test 26: large large-base digit`,
        "IS_BASEN 35 [15;33]",  returns "T";
`test 27: too-large large-base digit`,
        "IS_BASEN 31 [32;2]",   returns "F";
`test 28: too-large large-base digit`,
        "IS_BASEN 31 [9;32;2]", returns "F";
`test 29: too-large large-base digit`,
        "IS_BASEN 28 [0;2;32]", returns "F";
`test 30: too-large final digit`,
        "IS_BASEN 10 [5;11]",   returns "F";
`test 31: too-large first digit`,
        "IS_BASEN 10 [12;9]",   returns "F";
`test 32: too-large central digit`,
        "IS_BASEN 10 [3;41;7]", returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test IS_NORMALIZED_CONV `IS_NORMALIZED_CONV` relation [
`test 1: null list`,
        "IS_NORMALIZED []",                     returns "T";
`test 2: zero list`,
        "IS_NORMALIZED [0]",                    returns "F";
`test 3: many zeros`,
        "IS_NORMALIZED [0;0;0]",                returns "F";
`test 4: zero followed by nonzeros`,
        "IS_NORMALIZED [0;1;2;3;4]",            returns "F";
`test 5: single nonzero digit`,
        "IS_NORMALIZED [8]",                    returns "T";
`test 6: nonzero head`,
        "IS_NORMALIZED [1;0;0;0]",              returns "T";
`test 7: nonzero list`,
        "IS_NORMALIZED [5;1;2;4]",              returns "T";
`test 8: zero head with variable body`,
        "IS_NORMALIZED (CONS 0 x)",             returns "F";
`test 9: nonzero head with variable body`,
        "IS_NORMALIZED (CONS 1 x)",             returns "T"]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_NORMALIZE_CONV `BASEN_NORMALIZE_CONV` relation [
`test 1: normalize zero`,
        "BASEN 10 [0]",                         returns "BASEN 10 []";
`test 2: normalize lots of zeros`,
        "BASEN 10 [0;0;0;0;0;0;0;0;0;0]",       returns "BASEN 10 []";
`test 3: normalize a single-digit nonzero`,
        "BASEN 10 [0;3]",                       returns "BASEN 10 [3]";
`test 4: normalize a many-digit nonzero`,
        "BASEN 10 [0;1;2;3;4;5]",               returns "BASEN 10 [1;2;3;4;5]";
`test 5: normalize many leading zeros`,
        "BASEN 10 [0;0;0;0;4;5;6]",             returns "BASEN 10 [4;5;6]";
`test 6: normalize with nonzero in middle`,
        "BASEN 10 [0;0;0;8;0;0;0;0;0]",         returns "BASEN 10 [8;0;0;0;0;0]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test (uncurry BASEN_DENORMALIZE_CONV) `BASEN_DENORMALIZE_CONV` relation [
`test 1: denormalize zero`,
        (1, "BASEN 10 []"),             returns "BASEN 10 [0]";
`test 2: denormalize lots of zeros`,
        (10, "BASEN 10 []"),            returns "BASEN 10 [0;0;0;0;0;0;0;0;0;0]";
`test 3: denormalize with leading zeros`,
        (2, "BASEN 10 [0;0;3]"),        returns "BASEN 10 [0;0;0;0;3]";
`test 4: denormalize by none`,
        (0, "BASEN 10 [1;2;3;4;5]"),    returns "BASEN 10 [1;2;3;4;5]";
`test 5: denormalize negative`,
        (-4, "BASEN 10 [4;5;6]"),       returns "BASEN 10 [4;5;6]"]
where relation input actual expected =
  concl actual = mk_eq (snd input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_COMPARE_CONV `BASEN_COMPARE_CONV` relation [
`test 1: nil lists`,
        "BASEN 10 ([]: num list) = BASEN 10 ([]: num list)",
        returns "=: num -> num -> bool";
`test 2: nil vs. nonzero`,
        "BASEN 10 ([]: num list) < BASEN 10 [2]",
        returns "<";
`test 3: nonzero vs. nil`,
        "BASEN 10 [3] > BASEN 10 ([]: num list)",
        returns ">";
`test 4: nonzero vs. zero`,
        "BASEN 10 [22] <= BASEN 10 []",
        returns ">";
`test 5: less than`,
        "BASEN 10 [3;4;4] >= BASEN 10 [5;5;5]",
        returns "<";
`test 6: less than, nondecimal`,
        "BASEN 8 [2] * BASEN 8 [6;5;4;3;3]",
        returns "<";
`test 7: less than, weird base`,
        "BASEN 7 [1;1] DIV BASEN 7 [2;3]",
        returns "<";
`test 8: greater than`,
        "BASEN 10 [5;6;2] MOD BASEN 10 [5;5;5]",
        returns ">";
`test 9: greater than, nondecimal`,
        "BASEN 8 [7;7;7] < BASEN 8 [6;5;4]",
        returns ">";
`test 10: greater than, weird base`,
        "BASEN 7 [2;5] > BASEN 7 [2;3]",
        returns ">";
`test 11: equal`,
        "BASEN 10 [3;4;4] = BASEN 10 [3;4;4]",
        returns "=: num -> num -> bool";
`test 12: equal, nondecimal`,
        "BASEN 8 [2;6] = BASEN 8 [2;6]",
        returns "=: num -> num -> bool";
`test 13: equal, weird base`,
        "BASEN 7 [6;3;5;2] = BASEN 7 [6;3;5;2]",
        returns "=: num -> num -> bool" ]
where relation input actual expected =
  let left, right = (rand # I) (dest_comb input) in
  concl actual = mk_eq( mk_binary_comb expected left right, "T" )
and returns, failswith = inl, inr;;

sanity_test BASEN_EQ_CONV `BASEN_EQ_CONV` relation [
`test 1: equal`,
        "BASEN 10 [3;4;5] = BASEN 10 [3;4;5]",          returns "T";
`test 2: not equal in last digit`,
        "BASEN 2 [1;1;1;1] = BASEN 2 [1;1;1;0]",        returns "F";
`test 3: not equal and different lengths`,
        "BASEN 16 [8;10;14] = BASEN 16 [12;4]",         returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_LT_CONV `BASEN_LT_CONV` relation [
`test 1: less than in last digit`,
        "BASEN 2 [1;1;1;0] < BASEN 2 [1;1;1;1]",        returns "T";
`test 2: not less than despite being equal`,
        "BASEN 10 [3;4;5] < BASEN 10 [3;4;5]",          returns "F";
`test 3: not less than despite first digit being smaller`,
        "BASEN 16 [8;10;14] < BASEN 16 [12;4]",         returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_LE_CONV `BASEN_LE_CONV` relation [
`test 1: less than in last digit`,
        "BASEN 2 [1;1;1;0] <= BASEN 2 [1;1;1;1]",       returns "T";
`test 2: less or equal because equal`,
        "BASEN 10 [3;4;5] <= BASEN 10 [3;4;5]",         returns "T";
`test 3: not less than despite first digit being smaller`,
        "BASEN 16 [8;10;14] <= BASEN 16 [12;4]",        returns "F" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_GT_CONV `BASEN_GT_CONV` relation [
`test 1: not greater than in last digit`,
        "BASEN 2 [1;1;1;0] > BASEN 2 [1;1;1;1]",        returns "F";
`test 2: not greater than despite being equal`,
        "BASEN 10 [3;4;5] > BASEN 10 [3;4;5]",          returns "F";
`test 3: greater than despite first digit being smaller`,
        "BASEN 16 [8;10;14] > BASEN 16 [12;4]",         returns "T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_GE_CONV `BASEN_GE_CONV` relation [
`test 1: not greater than in last digit`,
        "BASEN 2 [1;1;1;0] >= BASEN 2 [1;1;1;1]",       returns "F";
`test 2: not greater than despite being equal`,
        "BASEN 10 [3;4;5] >= BASEN 10 [3;4;5]",         returns "T";
`test 3: greater than despite first digit being smaller`,
        "BASEN 16 [8;10;14] >= BASEN 16 [12;4]",        returns "T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test (uncurry fast_add) `fast_add` relation [
`test 1: an accelerated case`,
        (2,3),  returns "5";
`test 2: an unaccelerated case`,
        (256,2), returns "258" ]
where relation input actual expected =
  let addend, augend = (term_of_int # term_of_int) input in
  concl actual = mk_eq (mk_binary_comb "+" addend augend, expected)
and returns, failswith = inl, inr;;

sanity_test (uncurry (uncurry fast_add_with_carry)) `fast_add_with_carry` relation [
`test 1: an accelerated case`,
        ((2,3),1),      returns "6";
`test 2: an unaccelerated case`,
        ((256,2),9),    returns "267" ]
where relation input actual expected =
  let (addend, augend), carry =
    ((term_of_int # term_of_int) # term_of_int) input in
  concl actual =
    mk_eq ((mk_binary_comb "+" (mk_binary_comb "+" addend augend) carry), expected)
and returns, failswith = inl, inr;;

sanity_test (uncurry (uncurry fast_mul_with_carry)) `fast_mul_with_carry` relation [
`test 1: an accelerated case`,
        ((2,3),4),      returns "10";
`test 2: an unaccelerated case`,
        ((16,16),20),   returns "276" ]
where relation input actual expected =
  let (mand, mier), carry =
    ((term_of_int # term_of_int) # term_of_int) input in
  concl actual =
    mk_eq ((mk_binary_comb "+" (mk_binary_comb "*" mand mier) carry), expected)
and returns, failswith = inl, inr;;

sanity_test (uncurry fast_div_mod) `fast_div_mod` relation [
`test 1: an accelerated case`,
        (26, 10),       returns ("2","6");
`test 2: an unaccelerated case`,
        (26, 3),        returns ("8","2") ]
where relation input actual expected =
  let dend, dor = (term_of_int # term_of_int) input in
  let div_thm, mod_thm = actual in
  let quo, rem = expected in
  let div_result = mk_eq (mk_binary_comb "DIV" dend dor, quo) in
  let mod_result = mk_eq (mk_binary_comb "MOD" dend dor, rem) in
  (concl div_thm = div_result) & (concl mod_thm = mod_result)
and returns, failswith = inl, inr;;

sanity_test BASEN_ADD_CONV `BASEN_ADD_CONV` relation [
`test 1: null addend and null augend`,
        "BASEN 2 [] + BASEN 2 []",
        returns "BASEN 2 []";
`test 2: null addend and single-digit augend`,
        "BASEN 8 [] + BASEN 8 [7]",
        returns "BASEN 8 [7]";
`test 3: null addend and multi-digit augend`,
        "BASEN 10 [] + BASEN 10 [1;3;5]",
        returns "BASEN 10 [1;3;5]";
`test 4: single-digit addend and null augend`,
        "BASEN 16 [1] + BASEN 16 []",
        returns "BASEN 16 [1]";
`test 5: single-digit addend and single-digit augend`,
        "BASEN 10 [5] + BASEN 10 [9]",
        returns "BASEN 10 [1;4]";
`test 6: single-digit addend and multi-digit augend`,
        "BASEN 16 [7] + BASEN 16 [11;15;2;0;1]",
        returns "BASEN 16 [11;15;2;0;8]";
`test 7: multi-digit addend and null augend`,
        "BASEN 11 [1;3;5;7;9] + BASEN 11 []",
        returns "BASEN 11 [1;3;5;7;9]";
`test 8: multi-digit addend and single-digit augend`,
        "BASEN 10 [9;9;9;9] + BASEN 10 [3]",
        returns "BASEN 10 [1;0;0;0;2]";
`test 9: multi-digit addend and multi-digit augend`,
        "BASEN 10 [8;7;6;5;4] + BASEN 10 [1;2;3;4;5]",
        returns "BASEN 10 [9;9;9;9;9]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_SUC_CONV `BASEN_SUC_CONV` relation [
`test 1: any numeral`,
        "SUC (BASEN 10 [1;2;3])",       returns "BASEN 10 [1;2;4]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_SUB_CONV `BASEN_SUB_CONV` relation [
`test 1: something from zero`,
        "BASEN 2 [] - BASEN 2 [1;1;1]",
        returns "BASEN 2 []";
`test 2: equals`,
        "BASEN 10 [1;2;3] - BASEN 10 [1;2;3]",
        returns "BASEN 10 []";
`test 3: small from large`,
        "BASEN 16 [4;5;6;7] - BASEN 16 [1;2;3]",
        returns "BASEN 16 [4;4;4;4]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_PRE_CONV `BASEN_PRE_CONV` relation [
`test 1: any numeral`,
        "PRE (BASEN 10 [1;2;3])",       returns "BASEN 10 [1;2;2]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_MUL_CONV `BASEN_MUL_CONV` relation [
`test 1: zero multiplier and multiplicand`,
        "BASEN 10 [] * BASEN 10 []",
        returns "BASEN 10 []";
`test 2: zero multiplicand`,
        "BASEN 10 [] * BASEN 10 [3;4]",
        returns "BASEN 10 []";
`test 3: zero multiplier`,
        "BASEN 10 [3;4;5] * BASEN 10 []",
        returns "BASEN 10 []";
`test 4: nonzero product`,
        "BASEN 10 [2;3;4] * BASEN 10 [5;6;7;8]",
        returns "BASEN 10 [1;3;2;8;6;5;2]";
`test 5: base 16`,
        "BASEN 16 [1] * BASEN 16 [3]",
        returns "BASEN 16 [3]";
`test 6: long multiplicand`,
        "BASEN 16 [2;3;4;5;6;7;8;9;10] * BASEN 16 [3]",
        returns "BASEN 16 [6;9;13;0;3;6;9;12;14]";
`test 7: long multiplier`,
        "BASEN 16 [3;7] * BASEN 16 [1;2;3;4;5;6;7;8;9;10]",
        returns "BASEN 16[3;14;9;3;14;9;3;14;9;1;6]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_DIV_CONV `BASEN_DIV_CONV` relation [
`test 1: divide zero by something`,
        "BASEN 10 [] DIV BASEN 10 [1;2;3]",     returns "BASEN 10 []";
`test 2: divide something by 1`,
        "BASEN 10 [4;3;6] DIV BASEN 10 [1]",    returns "BASEN 10 [4;3;6]";
`test 3: divide something by itself`,
        "BASEN 16 [2;2;5] DIV BASEN 16 [2;2;5]", returns "BASEN 16 [1]";
`test 4: divide something by a factor of it`,
        "BASEN 10 [9;0;3] DIV BASEN 10 [2;1]",  returns "BASEN 10 [4;3]";
`test 5: divide leaving a remainder`,
        "BASEN 10 [9;0;3] DIV BASEN 10 [2;4]",  returns "BASEN 10 [3;7]";
`test 6: divide by something larger`,
        "BASEN 10 [9;0] DIV BASEN 10 [2;9;9]",  returns "BASEN 10 []" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_MOD_CONV `BASEN_MOD_CONV` relation [
`test 1: take the modulo of zero by something`,
        "BASEN 10 [] MOD BASEN 10 [1;2;3]",     returns "BASEN 10 []";
`test 2: take the modulo of something by 1`,
        "BASEN 10 [4;3;6] MOD BASEN 10 [1]",    returns "BASEN 10 []";
`test 3: take the modulo of something by itself`,
        "BASEN 16 [2;2;5] MOD BASEN 16 [2;2;5]", returns "BASEN 16 []";
`test 4: take the modulo of something by a factor of it`,
        "BASEN 10 [9;0;3] MOD BASEN 10 [2;1]",  returns "BASEN 10 []";
`test 5: take the modulo leaving a remainder`,
        "BASEN 10 [9;0;3] MOD BASEN 10 [2;4]",  returns "BASEN 10 [1;5]";
`test 6: take the modulo by something larger`,
        "BASEN 10 [9;0] MOD BASEN 10 [2;9;9]",  returns "BASEN 10 [9;0]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_EXP_CONV `BASEN_EXP_CONV` relation [
`test 1: zero exponand and exponent`,
        "BASEN 10 [] EXP BASEN 10 []",
        returns "BASEN 10 [1]" ;
`test 2: zero exponand and nonzero exponent`,
        "BASEN 10 [] EXP BASEN 10 [3]",
        returns "BASEN 10 []" ;
`test 3: nonzero exponand and zero exponent`,
        "BASEN 10 [1;5] EXP BASEN 10 []",
        returns "BASEN 10 [1]" ;
`test 4: exponent of 1`,
        "BASEN 10 [2;4;7] EXP BASEN 10 [1]",
        returns "BASEN 10 [2;4;7]" ;
`test 5: squaring`,
        "BASEN 8 [1;0] EXP BASEN 8 [2]",
        returns "BASEN 8 [1;0;0]" ;
`test 6: raising to a large power`,
        "BASEN 10 [2] EXP BASEN 10 [6;4]",
        returns "BASEN 10 [1;8;4;4;6;7;4;4;0;7;3;7;0;9;5;5;1;6;1;6]" ;
`test 7: raising a large number to a power`,
        "BASEN 10 [6;5;5;3;6] EXP BASEN 10 [4]",
        returns "BASEN 10 [1;8;4;4;6;7;4;4;0;7;3;7;0;9;5;5;1;6;1;6]" ;
`test 8: raising to a power with an assortment of bits`,
        "BASEN 16 [5] EXP BASEN 16 [1;12]",
        returns "BASEN 16 [2;0;4;15;12;14;5;14;3;14;2;5;0;2;6;1;1]" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

sanity_test BASEN_CONV `BASEN_CONV` relation [
`test 1: zero in an optimized radix`,
        "BASEN 10 []",          returns "0";
`test 2: zero in a non-optimized radix`,
        "BASEN 9 []",           returns "0";
`test 3: non-normalized zero in an optimized radix`,
        "BASEN 2 [0]",          returns "0";
`test 4: non-normalized zero in a non-optimized radix`,
        "BASEN 3 [0]",          returns "0";
`test 5: single-digit number in an optimized radix`,
        "BASEN 8 [7]",          returns "7";
`test 6: single-digit number in a non-optimized radix`,
        "BASEN 7 [1]",          returns "1";
`test 7: non-normalized single-digit number in an optimized radix`,
        "BASEN 16 [0;13]",      returns "13";
`test 8: non-normalized single-digit number in a non-optimized radix`,
        "BASEN 17 [0;16]",      returns "16";
`test 9: multi-digit number in an optimized radix`,
        "BASEN 10 [3;2]",       returns "32";
`test 10: multi-digit number in a non-optimized radix`,
        "BASEN 14 [1;4]",       returns "18";
`test 11: non-normalized multi-digit number in an optimized radix`,
        "BASEN 2 [0;1;0;0]",    returns "4";
`test 12: non-normalized multi-digit number in a non-optimized radix`,
        "BASEN 5 [0;2;1;1;1]",  returns "281" ]
where relation input actual expected =
  concl actual = mk_eq( input, expected )
and returns, failswith = inl, inr;;

sanity_test (uncurry BASEN_OF_NUM_CONV) `BASEN_OF_NUM_CONV` relation [
`test 1: zero in an optimized radix`,
        ("10", "0"),    returns "BASEN 10 []";
`test 2: zero in a non-optimized radix`,
        ("9", "0"),     returns "BASEN 9 []";
`test 3: single-digit number in an optimized radix`,
        ("8", "7"),     returns "BASEN 8 [7]";
`test 4: single-digit number in a non-optimized radix`,
        ("7", "1"),     returns "BASEN 7 [1]";
`test 5: multi-digit number in an optimized radix`,
        ("10", "32"),   returns "BASEN 10 [3;2]";
`test 6: multi-digit number in a non-optimized radix`,
        ("14", "18"),   returns "BASEN 14 [1;4]" ]
where relation input actual expected =
  concl actual = mk_eq( snd input, expected )
and returns, failswith = inl, inr;;

sanity_test NUM_ARITH_CONV `NUM_ARITH_CONV` relation [
`test 1: normalize`,
        "BASEN 10 [0;0;0;1;2;3]",
        returns "BASEN 10 [1;2;3]";
`test 2: add`,
        "BASEN 10 [9;8;7;6;5;4;3;2;1] + BASEN 10 [8;2;9;1;0;3;6;4;7;5]",
        returns "BASEN 10 [9;2;7;8;6;9;0;7;9;6]";
`test 3: sub`,
        "BASEN 10 [9;8;7;6;5;4;3;2;1] - BASEN 10 [8;2;9;1;0;3;6;4;7]",
        returns "BASEN 10 [1;5;8;5;5;0;6;7;4]";
`test 4: suc`,
        "SUC (BASEN 10 [9;8;7;6;5;4;3;2;1;9])",
        returns "BASEN 10 [9;8;7;6;5;4;3;2;2;0]";
`test 5: pre`,
        "PRE (BASEN 10 [9;8;7;6;5;4;3;2;1;0])",
        returns "BASEN 10 [9;8;7;6;5;4;3;2;0;9]";
`test 6: mul`,
        "BASEN 10 [9;8;7] * BASEN 10 [1;0;3]",
        returns "BASEN 10 [1;0;1;6;6;1]";
`test 7: div`,
        "BASEN 10 [9;8;7;6] DIV BASEN 10 [8;2;9]",
        returns "BASEN 10 [1;1]";
`test 8: mod`,
        "BASEN 10 [9;8;7;6] MOD BASEN 10 [8;2;9]",
        returns "BASEN 10 [7;5;7]";
`test 9: exp`,
        "BASEN 10 [1;2;3] EXP BASEN 10 [3]",
        returns "BASEN 10 [1;8;6;0;8;6;7]";
`test 10: lt`,
        "BASEN 10 [9;8;7;6;5;4;3;2;1] < BASEN 10 [8;2;9;1;0;3;6;4;7]",
        returns "F" ;
`test 11: complex expressions`,
        "((BASEN 10 [2;3] * BASEN 10 [5]) > BASEN 10 [4;5] DIV BASEN 10 [2]) /\
         (BASEN 16 [2;11] MOD BASEN 16 [5] = BASEN 16 [3]) /\
         (BASEN 2 [1;1;1;1;1;1;1;1] <= BASEN 2 [1;1;1] EXP BASEN 2 [1;1;0]) /\
         (PRE (BASEN 10 [1;0]) = SUC (BASEN 10 [8])) /\
         ((BASEN 10 [2] * BASEN 10 [3]) + BASEN 10 [4] = BASEN 10 [1;0])",
        returns "T /\ T /\ T /\ T /\ T" ]
where relation input actual expected =
  concl actual = mk_eq (input, expected)
and returns, failswith = inl, inr;;

