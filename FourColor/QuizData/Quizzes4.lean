/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Lit

/-!
# The quizzes of configurations 491 to 633

Part 4 of 4 of the check of the quizzes `cfquiz cf` of the 633 configurations (see
`FourColor.QuizData.Tree`):

* `qzNNN : Quiz` (for `NNN = 491, ..., 633`) is the literal value of `cfquiz cfNNN`, added by
  `#quizdata_quizzes 491 143`;
* `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` is checked by the kernel, one configuration per
  declaration, with `cfquiz_eq_of_cfquizCheck` and the radius certificate `i` (the kernel face
  with which the radius test `cpradius2` succeeds). The theorems were written by
  `#quizdata_print_checks 491 143`.

Checking one configuration per declaration keeps each kernel check small (at most about 0.2 s)
and is also faster in total than checking blocks of configurations together.
-/

namespace FourColor.QuizData

#quizdata_quizzes 491 143

@[quizdata_cfquiz] theorem cfquiz_cf491 : cfquiz cf491 = qz491 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf492 : cfquiz cf492 = qz492 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf493 : cfquiz cf493 = qz493 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf494 : cfquiz cf494 = qz494 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf495 : cfquiz cf495 = qz495 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf496 : cfquiz cf496 = qz496 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf497 : cfquiz cf497 = qz497 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf498 : cfquiz cf498 = qz498 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf499 : cfquiz cf499 = qz499 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf500 : cfquiz cf500 = qz500 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf501 : cfquiz cf501 = qz501 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf502 : cfquiz cf502 = qz502 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf503 : cfquiz cf503 = qz503 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf504 : cfquiz cf504 = qz504 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf505 : cfquiz cf505 = qz505 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf506 : cfquiz cf506 = qz506 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf507 : cfquiz cf507 = qz507 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf508 : cfquiz cf508 = qz508 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf509 : cfquiz cf509 = qz509 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf510 : cfquiz cf510 = qz510 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf511 : cfquiz cf511 = qz511 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf512 : cfquiz cf512 = qz512 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf513 : cfquiz cf513 = qz513 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf514 : cfquiz cf514 = qz514 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf515 : cfquiz cf515 = qz515 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf516 : cfquiz cf516 = qz516 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf517 : cfquiz cf517 = qz517 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf518 : cfquiz cf518 = qz518 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf519 : cfquiz cf519 = qz519 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf520 : cfquiz cf520 = qz520 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf521 : cfquiz cf521 = qz521 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf522 : cfquiz cf522 = qz522 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf523 : cfquiz cf523 = qz523 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf524 : cfquiz cf524 = qz524 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf525 : cfquiz cf525 = qz525 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf526 : cfquiz cf526 = qz526 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf527 : cfquiz cf527 = qz527 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf528 : cfquiz cf528 = qz528 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf529 : cfquiz cf529 = qz529 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf530 : cfquiz cf530 = qz530 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf531 : cfquiz cf531 = qz531 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf532 : cfquiz cf532 = qz532 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf533 : cfquiz cf533 = qz533 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf534 : cfquiz cf534 = qz534 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf535 : cfquiz cf535 = qz535 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf536 : cfquiz cf536 = qz536 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf537 : cfquiz cf537 = qz537 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf538 : cfquiz cf538 = qz538 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf539 : cfquiz cf539 = qz539 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf540 : cfquiz cf540 = qz540 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf541 : cfquiz cf541 = qz541 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf542 : cfquiz cf542 = qz542 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf543 : cfquiz cf543 = qz543 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf544 : cfquiz cf544 = qz544 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf545 : cfquiz cf545 = qz545 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf546 : cfquiz cf546 = qz546 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf547 : cfquiz cf547 = qz547 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf548 : cfquiz cf548 = qz548 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf549 : cfquiz cf549 = qz549 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf550 : cfquiz cf550 = qz550 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf551 : cfquiz cf551 = qz551 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf552 : cfquiz cf552 = qz552 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf553 : cfquiz cf553 = qz553 :=
  cfquiz_eq_of_cfquizCheck (i := 10) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf554 : cfquiz cf554 = qz554 :=
  cfquiz_eq_of_cfquizCheck (i := 10) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf555 : cfquiz cf555 = qz555 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf556 : cfquiz cf556 = qz556 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf557 : cfquiz cf557 = qz557 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf558 : cfquiz cf558 = qz558 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf559 : cfquiz cf559 = qz559 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf560 : cfquiz cf560 = qz560 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf561 : cfquiz cf561 = qz561 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf562 : cfquiz cf562 = qz562 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf563 : cfquiz cf563 = qz563 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf564 : cfquiz cf564 = qz564 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf565 : cfquiz cf565 = qz565 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf566 : cfquiz cf566 = qz566 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf567 : cfquiz cf567 = qz567 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf568 : cfquiz cf568 = qz568 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf569 : cfquiz cf569 = qz569 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf570 : cfquiz cf570 = qz570 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf571 : cfquiz cf571 = qz571 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf572 : cfquiz cf572 = qz572 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf573 : cfquiz cf573 = qz573 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf574 : cfquiz cf574 = qz574 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf575 : cfquiz cf575 = qz575 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf576 : cfquiz cf576 = qz576 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf577 : cfquiz cf577 = qz577 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf578 : cfquiz cf578 = qz578 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf579 : cfquiz cf579 = qz579 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf580 : cfquiz cf580 = qz580 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf581 : cfquiz cf581 = qz581 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf582 : cfquiz cf582 = qz582 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf583 : cfquiz cf583 = qz583 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf584 : cfquiz cf584 = qz584 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf585 : cfquiz cf585 = qz585 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf586 : cfquiz cf586 = qz586 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf587 : cfquiz cf587 = qz587 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf588 : cfquiz cf588 = qz588 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf589 : cfquiz cf589 = qz589 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf590 : cfquiz cf590 = qz590 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf591 : cfquiz cf591 = qz591 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf592 : cfquiz cf592 = qz592 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf593 : cfquiz cf593 = qz593 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf594 : cfquiz cf594 = qz594 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf595 : cfquiz cf595 = qz595 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf596 : cfquiz cf596 = qz596 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf597 : cfquiz cf597 = qz597 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf598 : cfquiz cf598 = qz598 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf599 : cfquiz cf599 = qz599 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf600 : cfquiz cf600 = qz600 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf601 : cfquiz cf601 = qz601 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf602 : cfquiz cf602 = qz602 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf603 : cfquiz cf603 = qz603 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf604 : cfquiz cf604 = qz604 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf605 : cfquiz cf605 = qz605 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf606 : cfquiz cf606 = qz606 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf607 : cfquiz cf607 = qz607 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf608 : cfquiz cf608 = qz608 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf609 : cfquiz cf609 = qz609 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf610 : cfquiz cf610 = qz610 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf611 : cfquiz cf611 = qz611 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf612 : cfquiz cf612 = qz612 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf613 : cfquiz cf613 = qz613 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf614 : cfquiz cf614 = qz614 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf615 : cfquiz cf615 = qz615 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf616 : cfquiz cf616 = qz616 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf617 : cfquiz cf617 = qz617 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf618 : cfquiz cf618 = qz618 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf619 : cfquiz cf619 = qz619 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf620 : cfquiz cf620 = qz620 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf621 : cfquiz cf621 = qz621 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf622 : cfquiz cf622 = qz622 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf623 : cfquiz cf623 = qz623 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf624 : cfquiz cf624 = qz624 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf625 : cfquiz cf625 = qz625 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf626 : cfquiz cf626 = qz626 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf627 : cfquiz cf627 = qz627 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf628 : cfquiz cf628 = qz628 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf629 : cfquiz cf629 = qz629 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf630 : cfquiz cf630 = qz630 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf631 : cfquiz cf631 = qz631 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf632 : cfquiz cf632 = qz632 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf633 : cfquiz cf633 = qz633 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)

end FourColor.QuizData
