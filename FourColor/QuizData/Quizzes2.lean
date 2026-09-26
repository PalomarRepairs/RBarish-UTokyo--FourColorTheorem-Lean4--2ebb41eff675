/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Lit

/-!
# The quizzes of configurations 191 to 330

Part 2 of 4 of the check of the quizzes `cfquiz cf` of the 633 configurations (see
`FourColor.QuizData.Tree`):

* `qzNNN : Quiz` (for `NNN = 191, ..., 330`) is the literal value of `cfquiz cfNNN`, added by
  `#quizdata_quizzes 191 140`;
* `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` is checked by the kernel, one configuration per
  declaration, with `cfquiz_eq_of_cfquizCheck` and the radius certificate `i` (the kernel face
  with which the radius test `cpradius2` succeeds). The theorems were written by
  `#quizdata_print_checks 191 140`.

Checking one configuration per declaration keeps each kernel check small (at most about 0.2 s)
and is also faster in total than checking blocks of configurations together.
-/

namespace FourColor.QuizData

#quizdata_quizzes 191 140

@[quizdata_cfquiz] theorem cfquiz_cf191 : cfquiz cf191 = qz191 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf192 : cfquiz cf192 = qz192 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf193 : cfquiz cf193 = qz193 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf194 : cfquiz cf194 = qz194 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf195 : cfquiz cf195 = qz195 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf196 : cfquiz cf196 = qz196 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf197 : cfquiz cf197 = qz197 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf198 : cfquiz cf198 = qz198 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf199 : cfquiz cf199 = qz199 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf200 : cfquiz cf200 = qz200 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf201 : cfquiz cf201 = qz201 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf202 : cfquiz cf202 = qz202 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf203 : cfquiz cf203 = qz203 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf204 : cfquiz cf204 = qz204 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf205 : cfquiz cf205 = qz205 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf206 : cfquiz cf206 = qz206 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf207 : cfquiz cf207 = qz207 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf208 : cfquiz cf208 = qz208 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf209 : cfquiz cf209 = qz209 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf210 : cfquiz cf210 = qz210 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf211 : cfquiz cf211 = qz211 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf212 : cfquiz cf212 = qz212 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf213 : cfquiz cf213 = qz213 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf214 : cfquiz cf214 = qz214 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf215 : cfquiz cf215 = qz215 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf216 : cfquiz cf216 = qz216 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf217 : cfquiz cf217 = qz217 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf218 : cfquiz cf218 = qz218 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf219 : cfquiz cf219 = qz219 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf220 : cfquiz cf220 = qz220 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf221 : cfquiz cf221 = qz221 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf222 : cfquiz cf222 = qz222 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf223 : cfquiz cf223 = qz223 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf224 : cfquiz cf224 = qz224 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf225 : cfquiz cf225 = qz225 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf226 : cfquiz cf226 = qz226 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf227 : cfquiz cf227 = qz227 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf228 : cfquiz cf228 = qz228 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf229 : cfquiz cf229 = qz229 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf230 : cfquiz cf230 = qz230 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf231 : cfquiz cf231 = qz231 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf232 : cfquiz cf232 = qz232 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf233 : cfquiz cf233 = qz233 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf234 : cfquiz cf234 = qz234 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf235 : cfquiz cf235 = qz235 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf236 : cfquiz cf236 = qz236 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf237 : cfquiz cf237 = qz237 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf238 : cfquiz cf238 = qz238 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf239 : cfquiz cf239 = qz239 :=
  cfquiz_eq_of_cfquizCheck (i := 10) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf240 : cfquiz cf240 = qz240 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf241 : cfquiz cf241 = qz241 :=
  cfquiz_eq_of_cfquizCheck (i := 10) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf242 : cfquiz cf242 = qz242 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf243 : cfquiz cf243 = qz243 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf244 : cfquiz cf244 = qz244 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf245 : cfquiz cf245 = qz245 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf246 : cfquiz cf246 = qz246 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf247 : cfquiz cf247 = qz247 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf248 : cfquiz cf248 = qz248 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf249 : cfquiz cf249 = qz249 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf250 : cfquiz cf250 = qz250 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf251 : cfquiz cf251 = qz251 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf252 : cfquiz cf252 = qz252 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf253 : cfquiz cf253 = qz253 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf254 : cfquiz cf254 = qz254 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf255 : cfquiz cf255 = qz255 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf256 : cfquiz cf256 = qz256 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf257 : cfquiz cf257 = qz257 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf258 : cfquiz cf258 = qz258 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf259 : cfquiz cf259 = qz259 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf260 : cfquiz cf260 = qz260 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf261 : cfquiz cf261 = qz261 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf262 : cfquiz cf262 = qz262 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf263 : cfquiz cf263 = qz263 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf264 : cfquiz cf264 = qz264 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf265 : cfquiz cf265 = qz265 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf266 : cfquiz cf266 = qz266 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf267 : cfquiz cf267 = qz267 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf268 : cfquiz cf268 = qz268 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf269 : cfquiz cf269 = qz269 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf270 : cfquiz cf270 = qz270 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf271 : cfquiz cf271 = qz271 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf272 : cfquiz cf272 = qz272 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf273 : cfquiz cf273 = qz273 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf274 : cfquiz cf274 = qz274 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf275 : cfquiz cf275 = qz275 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf276 : cfquiz cf276 = qz276 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf277 : cfquiz cf277 = qz277 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf278 : cfquiz cf278 = qz278 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf279 : cfquiz cf279 = qz279 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf280 : cfquiz cf280 = qz280 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf281 : cfquiz cf281 = qz281 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf282 : cfquiz cf282 = qz282 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf283 : cfquiz cf283 = qz283 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf284 : cfquiz cf284 = qz284 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf285 : cfquiz cf285 = qz285 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf286 : cfquiz cf286 = qz286 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf287 : cfquiz cf287 = qz287 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf288 : cfquiz cf288 = qz288 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf289 : cfquiz cf289 = qz289 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf290 : cfquiz cf290 = qz290 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf291 : cfquiz cf291 = qz291 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf292 : cfquiz cf292 = qz292 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf293 : cfquiz cf293 = qz293 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf294 : cfquiz cf294 = qz294 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf295 : cfquiz cf295 = qz295 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf296 : cfquiz cf296 = qz296 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf297 : cfquiz cf297 = qz297 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf298 : cfquiz cf298 = qz298 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf299 : cfquiz cf299 = qz299 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf300 : cfquiz cf300 = qz300 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf301 : cfquiz cf301 = qz301 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf302 : cfquiz cf302 = qz302 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf303 : cfquiz cf303 = qz303 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf304 : cfquiz cf304 = qz304 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf305 : cfquiz cf305 = qz305 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf306 : cfquiz cf306 = qz306 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf307 : cfquiz cf307 = qz307 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf308 : cfquiz cf308 = qz308 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf309 : cfquiz cf309 = qz309 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf310 : cfquiz cf310 = qz310 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf311 : cfquiz cf311 = qz311 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf312 : cfquiz cf312 = qz312 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf313 : cfquiz cf313 = qz313 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf314 : cfquiz cf314 = qz314 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf315 : cfquiz cf315 = qz315 :=
  cfquiz_eq_of_cfquizCheck (i := 10) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf316 : cfquiz cf316 = qz316 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf317 : cfquiz cf317 = qz317 :=
  cfquiz_eq_of_cfquizCheck (i := 11) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf318 : cfquiz cf318 = qz318 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf319 : cfquiz cf319 = qz319 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf320 : cfquiz cf320 = qz320 :=
  cfquiz_eq_of_cfquizCheck (i := 2) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf321 : cfquiz cf321 = qz321 :=
  cfquiz_eq_of_cfquizCheck (i := 0) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf322 : cfquiz cf322 = qz322 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf323 : cfquiz cf323 = qz323 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf324 : cfquiz cf324 = qz324 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf325 : cfquiz cf325 = qz325 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf326 : cfquiz cf326 = qz326 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf327 : cfquiz cf327 = qz327 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf328 : cfquiz cf328 = qz328 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf329 : cfquiz cf329 = qz329 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf330 : cfquiz cf330 = qz330 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)

end FourColor.QuizData
