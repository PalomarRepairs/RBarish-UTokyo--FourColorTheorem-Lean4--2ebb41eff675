/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Lit

/-!
# The quizzes of configurations 331 to 490

Part 3 of 4 of the check of the quizzes `cfquiz cf` of the 633 configurations (see
`FourColor.QuizData.Tree`):

* `qzNNN : Quiz` (for `NNN = 331, ..., 490`) is the literal value of `cfquiz cfNNN`, added by
  `#quizdata_quizzes 331 160`;
* `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` is checked by the kernel, one configuration per
  declaration, with `cfquiz_eq_of_cfquizCheck` and the radius certificate `i` (the kernel face
  with which the radius test `cpradius2` succeeds). The theorems were written by
  `#quizdata_print_checks 331 160`.

Checking one configuration per declaration keeps each kernel check small (at most about 0.2 s)
and is also faster in total than checking blocks of configurations together.
-/

namespace FourColor.QuizData

#quizdata_quizzes 331 160

@[quizdata_cfquiz] theorem cfquiz_cf331 : cfquiz cf331 = qz331 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf332 : cfquiz cf332 = qz332 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf333 : cfquiz cf333 = qz333 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf334 : cfquiz cf334 = qz334 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf335 : cfquiz cf335 = qz335 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf336 : cfquiz cf336 = qz336 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf337 : cfquiz cf337 = qz337 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf338 : cfquiz cf338 = qz338 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf339 : cfquiz cf339 = qz339 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf340 : cfquiz cf340 = qz340 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf341 : cfquiz cf341 = qz341 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf342 : cfquiz cf342 = qz342 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf343 : cfquiz cf343 = qz343 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf344 : cfquiz cf344 = qz344 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf345 : cfquiz cf345 = qz345 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf346 : cfquiz cf346 = qz346 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf347 : cfquiz cf347 = qz347 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf348 : cfquiz cf348 = qz348 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf349 : cfquiz cf349 = qz349 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf350 : cfquiz cf350 = qz350 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf351 : cfquiz cf351 = qz351 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf352 : cfquiz cf352 = qz352 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf353 : cfquiz cf353 = qz353 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf354 : cfquiz cf354 = qz354 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf355 : cfquiz cf355 = qz355 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf356 : cfquiz cf356 = qz356 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf357 : cfquiz cf357 = qz357 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf358 : cfquiz cf358 = qz358 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf359 : cfquiz cf359 = qz359 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf360 : cfquiz cf360 = qz360 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf361 : cfquiz cf361 = qz361 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf362 : cfquiz cf362 = qz362 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf363 : cfquiz cf363 = qz363 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf364 : cfquiz cf364 = qz364 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf365 : cfquiz cf365 = qz365 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf366 : cfquiz cf366 = qz366 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf367 : cfquiz cf367 = qz367 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf368 : cfquiz cf368 = qz368 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf369 : cfquiz cf369 = qz369 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf370 : cfquiz cf370 = qz370 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf371 : cfquiz cf371 = qz371 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf372 : cfquiz cf372 = qz372 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf373 : cfquiz cf373 = qz373 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf374 : cfquiz cf374 = qz374 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf375 : cfquiz cf375 = qz375 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf376 : cfquiz cf376 = qz376 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf377 : cfquiz cf377 = qz377 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf378 : cfquiz cf378 = qz378 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf379 : cfquiz cf379 = qz379 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf380 : cfquiz cf380 = qz380 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf381 : cfquiz cf381 = qz381 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf382 : cfquiz cf382 = qz382 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf383 : cfquiz cf383 = qz383 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf384 : cfquiz cf384 = qz384 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf385 : cfquiz cf385 = qz385 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf386 : cfquiz cf386 = qz386 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf387 : cfquiz cf387 = qz387 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf388 : cfquiz cf388 = qz388 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf389 : cfquiz cf389 = qz389 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf390 : cfquiz cf390 = qz390 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf391 : cfquiz cf391 = qz391 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf392 : cfquiz cf392 = qz392 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf393 : cfquiz cf393 = qz393 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf394 : cfquiz cf394 = qz394 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf395 : cfquiz cf395 = qz395 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf396 : cfquiz cf396 = qz396 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf397 : cfquiz cf397 = qz397 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf398 : cfquiz cf398 = qz398 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf399 : cfquiz cf399 = qz399 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf400 : cfquiz cf400 = qz400 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf401 : cfquiz cf401 = qz401 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf402 : cfquiz cf402 = qz402 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf403 : cfquiz cf403 = qz403 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf404 : cfquiz cf404 = qz404 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf405 : cfquiz cf405 = qz405 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf406 : cfquiz cf406 = qz406 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf407 : cfquiz cf407 = qz407 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf408 : cfquiz cf408 = qz408 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf409 : cfquiz cf409 = qz409 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf410 : cfquiz cf410 = qz410 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf411 : cfquiz cf411 = qz411 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf412 : cfquiz cf412 = qz412 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf413 : cfquiz cf413 = qz413 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf414 : cfquiz cf414 = qz414 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf415 : cfquiz cf415 = qz415 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf416 : cfquiz cf416 = qz416 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf417 : cfquiz cf417 = qz417 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf418 : cfquiz cf418 = qz418 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf419 : cfquiz cf419 = qz419 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf420 : cfquiz cf420 = qz420 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf421 : cfquiz cf421 = qz421 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf422 : cfquiz cf422 = qz422 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf423 : cfquiz cf423 = qz423 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf424 : cfquiz cf424 = qz424 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf425 : cfquiz cf425 = qz425 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf426 : cfquiz cf426 = qz426 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf427 : cfquiz cf427 = qz427 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf428 : cfquiz cf428 = qz428 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf429 : cfquiz cf429 = qz429 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf430 : cfquiz cf430 = qz430 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf431 : cfquiz cf431 = qz431 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf432 : cfquiz cf432 = qz432 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf433 : cfquiz cf433 = qz433 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf434 : cfquiz cf434 = qz434 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf435 : cfquiz cf435 = qz435 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf436 : cfquiz cf436 = qz436 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf437 : cfquiz cf437 = qz437 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf438 : cfquiz cf438 = qz438 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf439 : cfquiz cf439 = qz439 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf440 : cfquiz cf440 = qz440 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf441 : cfquiz cf441 = qz441 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf442 : cfquiz cf442 = qz442 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf443 : cfquiz cf443 = qz443 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf444 : cfquiz cf444 = qz444 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf445 : cfquiz cf445 = qz445 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf446 : cfquiz cf446 = qz446 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf447 : cfquiz cf447 = qz447 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf448 : cfquiz cf448 = qz448 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf449 : cfquiz cf449 = qz449 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf450 : cfquiz cf450 = qz450 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf451 : cfquiz cf451 = qz451 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf452 : cfquiz cf452 = qz452 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf453 : cfquiz cf453 = qz453 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf454 : cfquiz cf454 = qz454 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf455 : cfquiz cf455 = qz455 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf456 : cfquiz cf456 = qz456 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf457 : cfquiz cf457 = qz457 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf458 : cfquiz cf458 = qz458 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf459 : cfquiz cf459 = qz459 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf460 : cfquiz cf460 = qz460 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf461 : cfquiz cf461 = qz461 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf462 : cfquiz cf462 = qz462 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf463 : cfquiz cf463 = qz463 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf464 : cfquiz cf464 = qz464 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf465 : cfquiz cf465 = qz465 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf466 : cfquiz cf466 = qz466 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf467 : cfquiz cf467 = qz467 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf468 : cfquiz cf468 = qz468 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf469 : cfquiz cf469 = qz469 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf470 : cfquiz cf470 = qz470 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf471 : cfquiz cf471 = qz471 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf472 : cfquiz cf472 = qz472 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf473 : cfquiz cf473 = qz473 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf474 : cfquiz cf474 = qz474 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf475 : cfquiz cf475 = qz475 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf476 : cfquiz cf476 = qz476 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf477 : cfquiz cf477 = qz477 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf478 : cfquiz cf478 = qz478 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf479 : cfquiz cf479 = qz479 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf480 : cfquiz cf480 = qz480 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf481 : cfquiz cf481 = qz481 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf482 : cfquiz cf482 = qz482 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf483 : cfquiz cf483 = qz483 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf484 : cfquiz cf484 = qz484 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf485 : cfquiz cf485 = qz485 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf486 : cfquiz cf486 = qz486 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf487 : cfquiz cf487 = qz487 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf488 : cfquiz cf488 = qz488 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf489 : cfquiz cf489 = qz489 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf490 : cfquiz cf490 = qz490 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)

end FourColor.QuizData
