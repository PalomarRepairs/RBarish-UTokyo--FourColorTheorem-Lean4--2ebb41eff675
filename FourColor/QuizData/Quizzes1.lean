/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Lit

/-!
# The quizzes of configurations 1 to 190

Part 1 of 4 of the check of the quizzes `cfquiz cf` of the 633 configurations (see
`FourColor.QuizData.Tree`):

* `qzNNN : Quiz` (for `NNN = 001, ..., 190`) is the literal value of `cfquiz cfNNN`, added by
  `#quizdata_quizzes 1 190`;
* `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` is checked by the kernel, one configuration per
  declaration, with `cfquiz_eq_of_cfquizCheck` and the radius certificate `i` (the kernel face
  with which the radius test `cpradius2` succeeds). The theorems were written by
  `#quizdata_print_checks 1 190`.

Checking one configuration per declaration keeps each kernel check small (at most about 0.2 s)
and is also faster in total than checking blocks of configurations together.
-/

namespace FourColor.QuizData

#quizdata_quizzes 1 190

@[quizdata_cfquiz] theorem cfquiz_cf001 : cfquiz cf001 = qz001 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf002 : cfquiz cf002 = qz002 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf003 : cfquiz cf003 = qz003 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf004 : cfquiz cf004 = qz004 :=
  cfquiz_eq_of_cfquizCheck (i := 3) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf005 : cfquiz cf005 = qz005 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf006 : cfquiz cf006 = qz006 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf007 : cfquiz cf007 = qz007 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf008 : cfquiz cf008 = qz008 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf009 : cfquiz cf009 = qz009 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf010 : cfquiz cf010 = qz010 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf011 : cfquiz cf011 = qz011 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf012 : cfquiz cf012 = qz012 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf013 : cfquiz cf013 = qz013 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf014 : cfquiz cf014 = qz014 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf015 : cfquiz cf015 = qz015 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf016 : cfquiz cf016 = qz016 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf017 : cfquiz cf017 = qz017 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf018 : cfquiz cf018 = qz018 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf019 : cfquiz cf019 = qz019 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf020 : cfquiz cf020 = qz020 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf021 : cfquiz cf021 = qz021 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf022 : cfquiz cf022 = qz022 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf023 : cfquiz cf023 = qz023 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf024 : cfquiz cf024 = qz024 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf025 : cfquiz cf025 = qz025 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf026 : cfquiz cf026 = qz026 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf027 : cfquiz cf027 = qz027 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf028 : cfquiz cf028 = qz028 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf029 : cfquiz cf029 = qz029 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf030 : cfquiz cf030 = qz030 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf031 : cfquiz cf031 = qz031 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf032 : cfquiz cf032 = qz032 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf033 : cfquiz cf033 = qz033 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf034 : cfquiz cf034 = qz034 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf035 : cfquiz cf035 = qz035 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf036 : cfquiz cf036 = qz036 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf037 : cfquiz cf037 = qz037 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf038 : cfquiz cf038 = qz038 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf039 : cfquiz cf039 = qz039 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf040 : cfquiz cf040 = qz040 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf041 : cfquiz cf041 = qz041 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf042 : cfquiz cf042 = qz042 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf043 : cfquiz cf043 = qz043 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf044 : cfquiz cf044 = qz044 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf045 : cfquiz cf045 = qz045 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf046 : cfquiz cf046 = qz046 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf047 : cfquiz cf047 = qz047 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf048 : cfquiz cf048 = qz048 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf049 : cfquiz cf049 = qz049 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf050 : cfquiz cf050 = qz050 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf051 : cfquiz cf051 = qz051 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf052 : cfquiz cf052 = qz052 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf053 : cfquiz cf053 = qz053 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf054 : cfquiz cf054 = qz054 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf055 : cfquiz cf055 = qz055 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf056 : cfquiz cf056 = qz056 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf057 : cfquiz cf057 = qz057 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf058 : cfquiz cf058 = qz058 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf059 : cfquiz cf059 = qz059 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf060 : cfquiz cf060 = qz060 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf061 : cfquiz cf061 = qz061 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf062 : cfquiz cf062 = qz062 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf063 : cfquiz cf063 = qz063 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf064 : cfquiz cf064 = qz064 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf065 : cfquiz cf065 = qz065 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf066 : cfquiz cf066 = qz066 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf067 : cfquiz cf067 = qz067 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf068 : cfquiz cf068 = qz068 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf069 : cfquiz cf069 = qz069 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf070 : cfquiz cf070 = qz070 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf071 : cfquiz cf071 = qz071 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf072 : cfquiz cf072 = qz072 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf073 : cfquiz cf073 = qz073 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf074 : cfquiz cf074 = qz074 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf075 : cfquiz cf075 = qz075 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf076 : cfquiz cf076 = qz076 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf077 : cfquiz cf077 = qz077 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf078 : cfquiz cf078 = qz078 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf079 : cfquiz cf079 = qz079 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf080 : cfquiz cf080 = qz080 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf081 : cfquiz cf081 = qz081 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf082 : cfquiz cf082 = qz082 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf083 : cfquiz cf083 = qz083 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf084 : cfquiz cf084 = qz084 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf085 : cfquiz cf085 = qz085 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf086 : cfquiz cf086 = qz086 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf087 : cfquiz cf087 = qz087 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf088 : cfquiz cf088 = qz088 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf089 : cfquiz cf089 = qz089 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf090 : cfquiz cf090 = qz090 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf091 : cfquiz cf091 = qz091 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf092 : cfquiz cf092 = qz092 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf093 : cfquiz cf093 = qz093 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf094 : cfquiz cf094 = qz094 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf095 : cfquiz cf095 = qz095 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf096 : cfquiz cf096 = qz096 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf097 : cfquiz cf097 = qz097 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf098 : cfquiz cf098 = qz098 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf099 : cfquiz cf099 = qz099 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf100 : cfquiz cf100 = qz100 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf101 : cfquiz cf101 = qz101 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf102 : cfquiz cf102 = qz102 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf103 : cfquiz cf103 = qz103 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf104 : cfquiz cf104 = qz104 :=
  cfquiz_eq_of_cfquizCheck (i := 4) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf105 : cfquiz cf105 = qz105 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf106 : cfquiz cf106 = qz106 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf107 : cfquiz cf107 = qz107 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf108 : cfquiz cf108 = qz108 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf109 : cfquiz cf109 = qz109 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf110 : cfquiz cf110 = qz110 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf111 : cfquiz cf111 = qz111 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf112 : cfquiz cf112 = qz112 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf113 : cfquiz cf113 = qz113 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf114 : cfquiz cf114 = qz114 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf115 : cfquiz cf115 = qz115 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf116 : cfquiz cf116 = qz116 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf117 : cfquiz cf117 = qz117 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf118 : cfquiz cf118 = qz118 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf119 : cfquiz cf119 = qz119 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf120 : cfquiz cf120 = qz120 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf121 : cfquiz cf121 = qz121 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf122 : cfquiz cf122 = qz122 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf123 : cfquiz cf123 = qz123 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf124 : cfquiz cf124 = qz124 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf125 : cfquiz cf125 = qz125 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf126 : cfquiz cf126 = qz126 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf127 : cfquiz cf127 = qz127 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf128 : cfquiz cf128 = qz128 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf129 : cfquiz cf129 = qz129 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf130 : cfquiz cf130 = qz130 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf131 : cfquiz cf131 = qz131 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf132 : cfquiz cf132 = qz132 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf133 : cfquiz cf133 = qz133 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf134 : cfquiz cf134 = qz134 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf135 : cfquiz cf135 = qz135 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf136 : cfquiz cf136 = qz136 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf137 : cfquiz cf137 = qz137 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf138 : cfquiz cf138 = qz138 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf139 : cfquiz cf139 = qz139 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf140 : cfquiz cf140 = qz140 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf141 : cfquiz cf141 = qz141 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf142 : cfquiz cf142 = qz142 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf143 : cfquiz cf143 = qz143 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf144 : cfquiz cf144 = qz144 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf145 : cfquiz cf145 = qz145 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf146 : cfquiz cf146 = qz146 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf147 : cfquiz cf147 = qz147 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf148 : cfquiz cf148 = qz148 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf149 : cfquiz cf149 = qz149 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf150 : cfquiz cf150 = qz150 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf151 : cfquiz cf151 = qz151 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf152 : cfquiz cf152 = qz152 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf153 : cfquiz cf153 = qz153 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf154 : cfquiz cf154 = qz154 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf155 : cfquiz cf155 = qz155 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf156 : cfquiz cf156 = qz156 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf157 : cfquiz cf157 = qz157 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf158 : cfquiz cf158 = qz158 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf159 : cfquiz cf159 = qz159 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf160 : cfquiz cf160 = qz160 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf161 : cfquiz cf161 = qz161 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf162 : cfquiz cf162 = qz162 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf163 : cfquiz cf163 = qz163 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf164 : cfquiz cf164 = qz164 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf165 : cfquiz cf165 = qz165 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf166 : cfquiz cf166 = qz166 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf167 : cfquiz cf167 = qz167 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf168 : cfquiz cf168 = qz168 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf169 : cfquiz cf169 = qz169 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf170 : cfquiz cf170 = qz170 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf171 : cfquiz cf171 = qz171 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf172 : cfquiz cf172 = qz172 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf173 : cfquiz cf173 = qz173 :=
  cfquiz_eq_of_cfquizCheck (i := 8) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf174 : cfquiz cf174 = qz174 :=
  cfquiz_eq_of_cfquizCheck (i := 9) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf175 : cfquiz cf175 = qz175 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf176 : cfquiz cf176 = qz176 :=
  cfquiz_eq_of_cfquizCheck (i := 5) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf177 : cfquiz cf177 = qz177 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf178 : cfquiz cf178 = qz178 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf179 : cfquiz cf179 = qz179 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf180 : cfquiz cf180 = qz180 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf181 : cfquiz cf181 = qz181 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf182 : cfquiz cf182 = qz182 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf183 : cfquiz cf183 = qz183 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf184 : cfquiz cf184 = qz184 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf185 : cfquiz cf185 = qz185 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf186 : cfquiz cf186 = qz186 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf187 : cfquiz cf187 = qz187 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf188 : cfquiz cf188 = qz188 :=
  cfquiz_eq_of_cfquizCheck (i := 6) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf189 : cfquiz cf189 = qz189 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)
@[quizdata_cfquiz] theorem cfquiz_cf190 : cfquiz cf190 = qz190 :=
  cfquiz_eq_of_cfquizCheck (i := 7) (by decide +kernel)

end FourColor.QuizData
