/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfReducible
import FourColor.Reducibility.Cf001
import FourColor.Reducibility.Cf002
import FourColor.Reducibility.Cf003
import FourColor.Reducibility.Cf004
import FourColor.Reducibility.Cf005
import FourColor.Reducibility.Cf006
import FourColor.Reducibility.Cf007
import FourColor.Reducibility.Cf008
import FourColor.Reducibility.Cf009
import FourColor.Reducibility.Cf010
import FourColor.Reducibility.Cf011
import FourColor.Reducibility.Cf012
import FourColor.Reducibility.Cf013
import FourColor.Reducibility.Cf014
import FourColor.Reducibility.Cf015
import FourColor.Reducibility.Cf016
import FourColor.Reducibility.Cf017
import FourColor.Reducibility.Cf018
import FourColor.Reducibility.Cf019
import FourColor.Reducibility.Cf020
import FourColor.Reducibility.Cf021
import FourColor.Reducibility.Cf022
import FourColor.Reducibility.Cf023
import FourColor.Reducibility.Cf024
import FourColor.Reducibility.Cf025
import FourColor.Reducibility.Cf026
import FourColor.Reducibility.Cf027
import FourColor.Reducibility.Cf028
import FourColor.Reducibility.Cf029
import FourColor.Reducibility.Cf030
import FourColor.Reducibility.Cf031
import FourColor.Reducibility.Cf032
import FourColor.Reducibility.Cf033
import FourColor.Reducibility.Cf034
import FourColor.Reducibility.Cf035
import FourColor.Reducibility.Cf036
import FourColor.Reducibility.Cf037
import FourColor.Reducibility.Cf038
import FourColor.Reducibility.Cf039
import FourColor.Reducibility.Cf040
import FourColor.Reducibility.Cf041
import FourColor.Reducibility.Cf042
import FourColor.Reducibility.Cf043
import FourColor.Reducibility.Cf044
import FourColor.Reducibility.Cf045
import FourColor.Reducibility.Cf046
import FourColor.Reducibility.Cf047
import FourColor.Reducibility.Cf048
import FourColor.Reducibility.Cf049
import FourColor.Reducibility.Cf050
import FourColor.Reducibility.Cf051
import FourColor.Reducibility.Cf052
import FourColor.Reducibility.Cf053
import FourColor.Reducibility.Cf054
import FourColor.Reducibility.Cf055
import FourColor.Reducibility.Cf056
import FourColor.Reducibility.Cf057
import FourColor.Reducibility.Cf058
import FourColor.Reducibility.Cf059
import FourColor.Reducibility.Cf060
import FourColor.Reducibility.Cf061
import FourColor.Reducibility.Cf062
import FourColor.Reducibility.Cf063
import FourColor.Reducibility.Cf064
import FourColor.Reducibility.Cf065
import FourColor.Reducibility.Cf066
import FourColor.Reducibility.Cf067
import FourColor.Reducibility.Cf068
import FourColor.Reducibility.Cf069
import FourColor.Reducibility.Cf070
import FourColor.Reducibility.Cf071
import FourColor.Reducibility.Cf072
import FourColor.Reducibility.Cf073
import FourColor.Reducibility.Cf074
import FourColor.Reducibility.Cf075
import FourColor.Reducibility.Cf076
import FourColor.Reducibility.Cf077
import FourColor.Reducibility.Cf078
import FourColor.Reducibility.Cf079
import FourColor.Reducibility.Cf080
import FourColor.Reducibility.Cf081
import FourColor.Reducibility.Cf082
import FourColor.Reducibility.Cf083
import FourColor.Reducibility.Cf084
import FourColor.Reducibility.Cf085
import FourColor.Reducibility.Cf086
import FourColor.Reducibility.Cf087
import FourColor.Reducibility.Cf088
import FourColor.Reducibility.Cf089
import FourColor.Reducibility.Cf090
import FourColor.Reducibility.Cf091
import FourColor.Reducibility.Cf092
import FourColor.Reducibility.Cf093
import FourColor.Reducibility.Cf094
import FourColor.Reducibility.Cf095
import FourColor.Reducibility.Cf096
import FourColor.Reducibility.Cf097
import FourColor.Reducibility.Cf098
import FourColor.Reducibility.Cf099
import FourColor.Reducibility.Cf100
import FourColor.Reducibility.Cf101
import FourColor.Reducibility.Cf102
import FourColor.Reducibility.Cf103
import FourColor.Reducibility.Cf104
import FourColor.Reducibility.Cf105
import FourColor.Reducibility.Cf106
import FourColor.Reducibility.Cf107
import FourColor.Reducibility.Cf108
import FourColor.Reducibility.Cf109
import FourColor.Reducibility.Cf110
import FourColor.Reducibility.Cf111
import FourColor.Reducibility.Cf112
import FourColor.Reducibility.Cf113
import FourColor.Reducibility.Cf114
import FourColor.Reducibility.Cf115
import FourColor.Reducibility.Cf116
import FourColor.Reducibility.Cf117
import FourColor.Reducibility.Cf118
import FourColor.Reducibility.Cf119
import FourColor.Reducibility.Cf120
import FourColor.Reducibility.Cf121
import FourColor.Reducibility.Cf122
import FourColor.Reducibility.Cf123
import FourColor.Reducibility.Cf124
import FourColor.Reducibility.Cf125
import FourColor.Reducibility.Cf126
import FourColor.Reducibility.Cf127
import FourColor.Reducibility.Cf128
import FourColor.Reducibility.Cf129
import FourColor.Reducibility.Cf130
import FourColor.Reducibility.Cf131
import FourColor.Reducibility.Cf132
import FourColor.Reducibility.Cf133
import FourColor.Reducibility.Cf134
import FourColor.Reducibility.Cf135
import FourColor.Reducibility.Cf136
import FourColor.Reducibility.Cf137
import FourColor.Reducibility.Cf138
import FourColor.Reducibility.Cf139
import FourColor.Reducibility.Cf140
import FourColor.Reducibility.Cf141
import FourColor.Reducibility.Cf142
import FourColor.Reducibility.Cf143
import FourColor.Reducibility.Cf144
import FourColor.Reducibility.Cf145
import FourColor.Reducibility.Cf146
import FourColor.Reducibility.Cf147
import FourColor.Reducibility.Cf148
import FourColor.Reducibility.Cf149
import FourColor.Reducibility.Cf150
import FourColor.Reducibility.Cf151
import FourColor.Reducibility.Cf152
import FourColor.Reducibility.Cf153
import FourColor.Reducibility.Cf154
import FourColor.Reducibility.Cf155
import FourColor.Reducibility.Cf156
import FourColor.Reducibility.Cf157
import FourColor.Reducibility.Cf158
import FourColor.Reducibility.Cf159
import FourColor.Reducibility.Cf160
import FourColor.Reducibility.Cf161
import FourColor.Reducibility.Cf162
import FourColor.Reducibility.Cf163
import FourColor.Reducibility.Cf164
import FourColor.Reducibility.Cf165
import FourColor.Reducibility.Cf166
import FourColor.Reducibility.Cf167
import FourColor.Reducibility.Cf168
import FourColor.Reducibility.Cf169
import FourColor.Reducibility.Cf170
import FourColor.Reducibility.Cf171
import FourColor.Reducibility.Cf172
import FourColor.Reducibility.Cf173
import FourColor.Reducibility.Cf174
import FourColor.Reducibility.Cf175
import FourColor.Reducibility.Cf176
import FourColor.Reducibility.Cf177
import FourColor.Reducibility.Cf178
import FourColor.Reducibility.Cf179
import FourColor.Reducibility.Cf180
import FourColor.Reducibility.Cf181
import FourColor.Reducibility.Cf182
import FourColor.Reducibility.Cf183
import FourColor.Reducibility.Cf184
import FourColor.Reducibility.Cf185
import FourColor.Reducibility.Cf186
import FourColor.Reducibility.Cf187
import FourColor.Reducibility.Cf188
import FourColor.Reducibility.Cf189
import FourColor.Reducibility.Cf190
import FourColor.Reducibility.Cf191
import FourColor.Reducibility.Cf192
import FourColor.Reducibility.Cf193
import FourColor.Reducibility.Cf194
import FourColor.Reducibility.Cf195
import FourColor.Reducibility.Cf196
import FourColor.Reducibility.Cf197
import FourColor.Reducibility.Cf198
import FourColor.Reducibility.Cf199
import FourColor.Reducibility.Cf200
import FourColor.Reducibility.Cf201
import FourColor.Reducibility.Cf202
import FourColor.Reducibility.Cf203
import FourColor.Reducibility.Cf204
import FourColor.Reducibility.Cf205
import FourColor.Reducibility.Cf206
import FourColor.Reducibility.Cf207
import FourColor.Reducibility.Cf208
import FourColor.Reducibility.Cf209
import FourColor.Reducibility.Cf210
import FourColor.Reducibility.Cf211
import FourColor.Reducibility.Cf212
import FourColor.Reducibility.Cf213
import FourColor.Reducibility.Cf214
import FourColor.Reducibility.Cf215
import FourColor.Reducibility.Cf216
import FourColor.Reducibility.Cf217
import FourColor.Reducibility.Cf218
import FourColor.Reducibility.Cf219
import FourColor.Reducibility.Cf220
import FourColor.Reducibility.Cf221
import FourColor.Reducibility.Cf222
import FourColor.Reducibility.Cf223
import FourColor.Reducibility.Cf224
import FourColor.Reducibility.Cf225
import FourColor.Reducibility.Cf226
import FourColor.Reducibility.Cf227
import FourColor.Reducibility.Cf228
import FourColor.Reducibility.Cf229
import FourColor.Reducibility.Cf230
import FourColor.Reducibility.Cf231
import FourColor.Reducibility.Cf232
import FourColor.Reducibility.Cf233
import FourColor.Reducibility.Cf234
import FourColor.Reducibility.Cf235
import FourColor.Reducibility.Cf236
import FourColor.Reducibility.Cf237
import FourColor.Reducibility.Cf238
import FourColor.Reducibility.Cf239
import FourColor.Reducibility.Cf240
import FourColor.Reducibility.Cf241
import FourColor.Reducibility.Cf242
import FourColor.Reducibility.Cf243
import FourColor.Reducibility.Cf244
import FourColor.Reducibility.Cf245
import FourColor.Reducibility.Cf246
import FourColor.Reducibility.Cf247
import FourColor.Reducibility.Cf248
import FourColor.Reducibility.Cf249
import FourColor.Reducibility.Cf250
import FourColor.Reducibility.Cf251
import FourColor.Reducibility.Cf252
import FourColor.Reducibility.Cf253
import FourColor.Reducibility.Cf254
import FourColor.Reducibility.Cf255
import FourColor.Reducibility.Cf256
import FourColor.Reducibility.Cf257
import FourColor.Reducibility.Cf258
import FourColor.Reducibility.Cf259
import FourColor.Reducibility.Cf260
import FourColor.Reducibility.Cf261
import FourColor.Reducibility.Cf262
import FourColor.Reducibility.Cf263
import FourColor.Reducibility.Cf264
import FourColor.Reducibility.Cf265
import FourColor.Reducibility.Cf266
import FourColor.Reducibility.Cf267
import FourColor.Reducibility.Cf268
import FourColor.Reducibility.Cf269
import FourColor.Reducibility.Cf270
import FourColor.Reducibility.Cf271
import FourColor.Reducibility.Cf272
import FourColor.Reducibility.Cf273
import FourColor.Reducibility.Cf274
import FourColor.Reducibility.Cf275
import FourColor.Reducibility.Cf276
import FourColor.Reducibility.Cf277
import FourColor.Reducibility.Cf278
import FourColor.Reducibility.Cf279
import FourColor.Reducibility.Cf280
import FourColor.Reducibility.Cf281
import FourColor.Reducibility.Cf282
import FourColor.Reducibility.Cf283
import FourColor.Reducibility.Cf284
import FourColor.Reducibility.Cf285
import FourColor.Reducibility.Cf286
import FourColor.Reducibility.Cf287
import FourColor.Reducibility.Cf288
import FourColor.Reducibility.Cf289
import FourColor.Reducibility.Cf290
import FourColor.Reducibility.Cf291
import FourColor.Reducibility.Cf292
import FourColor.Reducibility.Cf293
import FourColor.Reducibility.Cf294
import FourColor.Reducibility.Cf295
import FourColor.Reducibility.Cf296
import FourColor.Reducibility.Cf297
import FourColor.Reducibility.Cf298
import FourColor.Reducibility.Cf299
import FourColor.Reducibility.Cf300
import FourColor.Reducibility.Cf301
import FourColor.Reducibility.Cf302
import FourColor.Reducibility.Cf303
import FourColor.Reducibility.Cf304
import FourColor.Reducibility.Cf305
import FourColor.Reducibility.Cf306
import FourColor.Reducibility.Cf307
import FourColor.Reducibility.Cf308
import FourColor.Reducibility.Cf309
import FourColor.Reducibility.Cf310
import FourColor.Reducibility.Cf311
import FourColor.Reducibility.Cf312
import FourColor.Reducibility.Cf313
import FourColor.Reducibility.Cf314
import FourColor.Reducibility.Cf315
import FourColor.Reducibility.Cf316
import FourColor.Reducibility.Cf317
import FourColor.Reducibility.Cf318
import FourColor.Reducibility.Cf319
import FourColor.Reducibility.Cf320
import FourColor.Reducibility.Cf321
import FourColor.Reducibility.Cf322
import FourColor.Reducibility.Cf323
import FourColor.Reducibility.Cf324
import FourColor.Reducibility.Cf325
import FourColor.Reducibility.Cf326
import FourColor.Reducibility.Cf327
import FourColor.Reducibility.Cf328
import FourColor.Reducibility.Cf329
import FourColor.Reducibility.Cf330
import FourColor.Reducibility.Cf331
import FourColor.Reducibility.Cf332
import FourColor.Reducibility.Cf333
import FourColor.Reducibility.Cf334
import FourColor.Reducibility.Cf335
import FourColor.Reducibility.Cf336
import FourColor.Reducibility.Cf337
import FourColor.Reducibility.Cf338
import FourColor.Reducibility.Cf339
import FourColor.Reducibility.Cf340
import FourColor.Reducibility.Cf341
import FourColor.Reducibility.Cf342
import FourColor.Reducibility.Cf343
import FourColor.Reducibility.Cf344
import FourColor.Reducibility.Cf345
import FourColor.Reducibility.Cf346
import FourColor.Reducibility.Cf347
import FourColor.Reducibility.Cf348
import FourColor.Reducibility.Cf349
import FourColor.Reducibility.Cf350
import FourColor.Reducibility.Cf351
import FourColor.Reducibility.Cf352
import FourColor.Reducibility.Cf353
import FourColor.Reducibility.Cf354
import FourColor.Reducibility.Cf355
import FourColor.Reducibility.Cf356
import FourColor.Reducibility.Cf357
import FourColor.Reducibility.Cf358
import FourColor.Reducibility.Cf359
import FourColor.Reducibility.Cf360
import FourColor.Reducibility.Cf361
import FourColor.Reducibility.Cf362
import FourColor.Reducibility.Cf363
import FourColor.Reducibility.Cf364
import FourColor.Reducibility.Cf365
import FourColor.Reducibility.Cf366
import FourColor.Reducibility.Cf367
import FourColor.Reducibility.Cf368
import FourColor.Reducibility.Cf369
import FourColor.Reducibility.Cf370
import FourColor.Reducibility.Cf371
import FourColor.Reducibility.Cf372
import FourColor.Reducibility.Cf373
import FourColor.Reducibility.Cf374
import FourColor.Reducibility.Cf375
import FourColor.Reducibility.Cf376
import FourColor.Reducibility.Cf377
import FourColor.Reducibility.Cf378
import FourColor.Reducibility.Cf379
import FourColor.Reducibility.Cf380
import FourColor.Reducibility.Cf381
import FourColor.Reducibility.Cf382
import FourColor.Reducibility.Cf383
import FourColor.Reducibility.Cf384
import FourColor.Reducibility.Cf385
import FourColor.Reducibility.Cf386
import FourColor.Reducibility.Cf387
import FourColor.Reducibility.Cf388
import FourColor.Reducibility.Cf389
import FourColor.Reducibility.Cf390
import FourColor.Reducibility.Cf391
import FourColor.Reducibility.Cf392
import FourColor.Reducibility.Cf393
import FourColor.Reducibility.Cf394
import FourColor.Reducibility.Cf395
import FourColor.Reducibility.Cf396
import FourColor.Reducibility.Cf397
import FourColor.Reducibility.Cf398
import FourColor.Reducibility.Cf399
import FourColor.Reducibility.Cf400
import FourColor.Reducibility.Cf401
import FourColor.Reducibility.Cf402
import FourColor.Reducibility.Cf403
import FourColor.Reducibility.Cf404
import FourColor.Reducibility.Cf405
import FourColor.Reducibility.Cf406
import FourColor.Reducibility.Cf407
import FourColor.Reducibility.Cf408
import FourColor.Reducibility.Cf409
import FourColor.Reducibility.Cf410
import FourColor.Reducibility.Cf411
import FourColor.Reducibility.Cf412
import FourColor.Reducibility.Cf413
import FourColor.Reducibility.Cf414
import FourColor.Reducibility.Cf415
import FourColor.Reducibility.Cf416
import FourColor.Reducibility.Cf417
import FourColor.Reducibility.Cf418
import FourColor.Reducibility.Cf419
import FourColor.Reducibility.Cf420
import FourColor.Reducibility.Cf421
import FourColor.Reducibility.Cf422
import FourColor.Reducibility.Cf423
import FourColor.Reducibility.Cf424
import FourColor.Reducibility.Cf425
import FourColor.Reducibility.Cf426
import FourColor.Reducibility.Cf427
import FourColor.Reducibility.Cf428
import FourColor.Reducibility.Cf429
import FourColor.Reducibility.Cf430
import FourColor.Reducibility.Cf431
import FourColor.Reducibility.Cf432
import FourColor.Reducibility.Cf433
import FourColor.Reducibility.Cf434
import FourColor.Reducibility.Cf435
import FourColor.Reducibility.Cf436
import FourColor.Reducibility.Cf437
import FourColor.Reducibility.Cf438
import FourColor.Reducibility.Cf439
import FourColor.Reducibility.Cf440
import FourColor.Reducibility.Cf441
import FourColor.Reducibility.Cf442
import FourColor.Reducibility.Cf443
import FourColor.Reducibility.Cf444
import FourColor.Reducibility.Cf445
import FourColor.Reducibility.Cf446
import FourColor.Reducibility.Cf447
import FourColor.Reducibility.Cf448
import FourColor.Reducibility.Cf449
import FourColor.Reducibility.Cf450
import FourColor.Reducibility.Cf451
import FourColor.Reducibility.Cf452
import FourColor.Reducibility.Cf453
import FourColor.Reducibility.Cf454
import FourColor.Reducibility.Cf455
import FourColor.Reducibility.Cf456
import FourColor.Reducibility.Cf457
import FourColor.Reducibility.Cf458
import FourColor.Reducibility.Cf459
import FourColor.Reducibility.Cf460
import FourColor.Reducibility.Cf461
import FourColor.Reducibility.Cf462
import FourColor.Reducibility.Cf463
import FourColor.Reducibility.Cf464
import FourColor.Reducibility.Cf465
import FourColor.Reducibility.Cf466
import FourColor.Reducibility.Cf467
import FourColor.Reducibility.Cf468
import FourColor.Reducibility.Cf469
import FourColor.Reducibility.Cf470
import FourColor.Reducibility.Cf471
import FourColor.Reducibility.Cf472
import FourColor.Reducibility.Cf473
import FourColor.Reducibility.Cf474
import FourColor.Reducibility.Cf475
import FourColor.Reducibility.Cf476
import FourColor.Reducibility.Cf477
import FourColor.Reducibility.Cf478
import FourColor.Reducibility.Cf479
import FourColor.Reducibility.Cf480
import FourColor.Reducibility.Cf481
import FourColor.Reducibility.Cf482
import FourColor.Reducibility.Cf483
import FourColor.Reducibility.Cf484
import FourColor.Reducibility.Cf485
import FourColor.Reducibility.Cf486
import FourColor.Reducibility.Cf487
import FourColor.Reducibility.Cf488
import FourColor.Reducibility.Cf489
import FourColor.Reducibility.Cf490
import FourColor.Reducibility.Cf491
import FourColor.Reducibility.Cf492
import FourColor.Reducibility.Cf493
import FourColor.Reducibility.Cf494
import FourColor.Reducibility.Cf495
import FourColor.Reducibility.Cf496
import FourColor.Reducibility.Cf497
import FourColor.Reducibility.Cf498
import FourColor.Reducibility.Cf499
import FourColor.Reducibility.Cf500
import FourColor.Reducibility.Cf501
import FourColor.Reducibility.Cf502
import FourColor.Reducibility.Cf503
import FourColor.Reducibility.Cf504
import FourColor.Reducibility.Cf505
import FourColor.Reducibility.Cf506
import FourColor.Reducibility.Cf507
import FourColor.Reducibility.Cf508
import FourColor.Reducibility.Cf509
import FourColor.Reducibility.Cf510
import FourColor.Reducibility.Cf511
import FourColor.Reducibility.Cf512
import FourColor.Reducibility.Cf513
import FourColor.Reducibility.Cf514
import FourColor.Reducibility.Cf515
import FourColor.Reducibility.Cf516
import FourColor.Reducibility.Cf517
import FourColor.Reducibility.Cf518
import FourColor.Reducibility.Cf519
import FourColor.Reducibility.Cf520
import FourColor.Reducibility.Cf521
import FourColor.Reducibility.Cf522
import FourColor.Reducibility.Cf523
import FourColor.Reducibility.Cf524
import FourColor.Reducibility.Cf525
import FourColor.Reducibility.Cf526
import FourColor.Reducibility.Cf527
import FourColor.Reducibility.Cf528
import FourColor.Reducibility.Cf529
import FourColor.Reducibility.Cf530
import FourColor.Reducibility.Cf531
import FourColor.Reducibility.Cf532
import FourColor.Reducibility.Cf533
import FourColor.Reducibility.Cf534
import FourColor.Reducibility.Cf535
import FourColor.Reducibility.Cf536
import FourColor.Reducibility.Cf537
import FourColor.Reducibility.Cf538
import FourColor.Reducibility.Cf539
import FourColor.Reducibility.Cf540
import FourColor.Reducibility.Cf541
import FourColor.Reducibility.Cf542
import FourColor.Reducibility.Cf543
import FourColor.Reducibility.Cf544
import FourColor.Reducibility.Cf545
import FourColor.Reducibility.Cf546
import FourColor.Reducibility.Cf547
import FourColor.Reducibility.Cf548
import FourColor.Reducibility.Cf549
import FourColor.Reducibility.Cf550
import FourColor.Reducibility.Cf551
import FourColor.Reducibility.Cf552
import FourColor.Reducibility.Cf553
import FourColor.Reducibility.Cf554
import FourColor.Reducibility.Cf555
import FourColor.Reducibility.Cf556
import FourColor.Reducibility.Cf557
import FourColor.Reducibility.Cf558
import FourColor.Reducibility.Cf559
import FourColor.Reducibility.Cf560
import FourColor.Reducibility.Cf561
import FourColor.Reducibility.Cf562
import FourColor.Reducibility.Cf563
import FourColor.Reducibility.Cf564
import FourColor.Reducibility.Cf565
import FourColor.Reducibility.Cf566
import FourColor.Reducibility.Cf567
import FourColor.Reducibility.Cf568
import FourColor.Reducibility.Cf569
import FourColor.Reducibility.Cf570
import FourColor.Reducibility.Cf571
import FourColor.Reducibility.Cf572
import FourColor.Reducibility.Cf573
import FourColor.Reducibility.Cf574
import FourColor.Reducibility.Cf575
import FourColor.Reducibility.Cf576
import FourColor.Reducibility.Cf577
import FourColor.Reducibility.Cf578
import FourColor.Reducibility.Cf579
import FourColor.Reducibility.Cf580
import FourColor.Reducibility.Cf581
import FourColor.Reducibility.Cf582
import FourColor.Reducibility.Cf583
import FourColor.Reducibility.Cf584
import FourColor.Reducibility.Cf585
import FourColor.Reducibility.Cf586
import FourColor.Reducibility.Cf587
import FourColor.Reducibility.Cf588
import FourColor.Reducibility.Cf589
import FourColor.Reducibility.Cf590
import FourColor.Reducibility.Cf591
import FourColor.Reducibility.Cf592
import FourColor.Reducibility.Cf593
import FourColor.Reducibility.Cf594
import FourColor.Reducibility.Cf595
import FourColor.Reducibility.Cf596
import FourColor.Reducibility.Cf597
import FourColor.Reducibility.Cf598
import FourColor.Reducibility.Cf599
import FourColor.Reducibility.Cf600
import FourColor.Reducibility.Cf601
import FourColor.Reducibility.Cf602
import FourColor.Reducibility.Cf603
import FourColor.Reducibility.Cf604
import FourColor.Reducibility.Cf605
import FourColor.Reducibility.Cf606
import FourColor.Reducibility.Cf607
import FourColor.Reducibility.Cf608
import FourColor.Reducibility.Cf609
import FourColor.Reducibility.Cf610
import FourColor.Reducibility.Cf611
import FourColor.Reducibility.Cf612
import FourColor.Reducibility.Cf613
import FourColor.Reducibility.Cf614
import FourColor.Reducibility.Cf615
import FourColor.Reducibility.Cf616
import FourColor.Reducibility.Cf617
import FourColor.Reducibility.Cf618
import FourColor.Reducibility.Cf619
import FourColor.Reducibility.Cf620
import FourColor.Reducibility.Cf621
import FourColor.Reducibility.Cf622
import FourColor.Reducibility.Cf623
import FourColor.Reducibility.Cf624
import FourColor.Reducibility.Cf625
import FourColor.Reducibility.Cf626
import FourColor.Reducibility.Cf627
import FourColor.Reducibility.Cf628
import FourColor.Reducibility.Cf629
import FourColor.Reducibility.Cf630
import FourColor.Reducibility.Cf631
import FourColor.Reducibility.Cf632
import FourColor.Reducibility.Cf633

/-!
# C-reducibility of the 633 configurations (port of `reducibility.v`)

`theReducibility` (math-comp `the_reducibility : reducibility`, where `present.v` defines
`reducibility := reducible_in_range 0 (size the_configs) the_configs`): every configuration of
`theConfigs` is C-reducible.  It collates the certificates `cfNNN_reducible` of the generated
modules `FourColor/Reducibility/CfNNN.lean` (the replacement for the `job*`/`task*` files).

This file is generated by `scripts/build_reducibility.sh gen`.
-/

namespace FourColor

set_option maxRecDepth 8000 in
/-- The configurations of indices 0 … 31 are C-reducible. -/
theorem reducibleBlock0 : ReducibleInRange 0 32 theConfigs :=
  reducible_in_range_cons cf001_reducible <|
  reducible_in_range_cons cf002_reducible <|
  reducible_in_range_cons cf003_reducible <|
  reducible_in_range_cons cf004_reducible <|
  reducible_in_range_cons cf005_reducible <|
  reducible_in_range_cons cf006_reducible <|
  reducible_in_range_cons cf007_reducible <|
  reducible_in_range_cons cf008_reducible <|
  reducible_in_range_cons cf009_reducible <|
  reducible_in_range_cons cf010_reducible <|
  reducible_in_range_cons cf011_reducible <|
  reducible_in_range_cons cf012_reducible <|
  reducible_in_range_cons cf013_reducible <|
  reducible_in_range_cons cf014_reducible <|
  reducible_in_range_cons cf015_reducible <|
  reducible_in_range_cons cf016_reducible <|
  reducible_in_range_cons cf017_reducible <|
  reducible_in_range_cons cf018_reducible <|
  reducible_in_range_cons cf019_reducible <|
  reducible_in_range_cons cf020_reducible <|
  reducible_in_range_cons cf021_reducible <|
  reducible_in_range_cons cf022_reducible <|
  reducible_in_range_cons cf023_reducible <|
  reducible_in_range_cons cf024_reducible <|
  reducible_in_range_cons cf025_reducible <|
  reducible_in_range_cons cf026_reducible <|
  reducible_in_range_cons cf027_reducible <|
  reducible_in_range_cons cf028_reducible <|
  reducible_in_range_cons cf029_reducible <|
  reducible_in_range_cons cf030_reducible <|
  reducible_in_range_cons cf031_reducible <|
  reducible_in_range_cons cf032_reducible <|
  reducible_in_range_nil 32 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 32 … 63 are C-reducible. -/
theorem reducibleBlock1 : ReducibleInRange 32 64 theConfigs :=
  reducible_in_range_cons cf033_reducible <|
  reducible_in_range_cons cf034_reducible <|
  reducible_in_range_cons cf035_reducible <|
  reducible_in_range_cons cf036_reducible <|
  reducible_in_range_cons cf037_reducible <|
  reducible_in_range_cons cf038_reducible <|
  reducible_in_range_cons cf039_reducible <|
  reducible_in_range_cons cf040_reducible <|
  reducible_in_range_cons cf041_reducible <|
  reducible_in_range_cons cf042_reducible <|
  reducible_in_range_cons cf043_reducible <|
  reducible_in_range_cons cf044_reducible <|
  reducible_in_range_cons cf045_reducible <|
  reducible_in_range_cons cf046_reducible <|
  reducible_in_range_cons cf047_reducible <|
  reducible_in_range_cons cf048_reducible <|
  reducible_in_range_cons cf049_reducible <|
  reducible_in_range_cons cf050_reducible <|
  reducible_in_range_cons cf051_reducible <|
  reducible_in_range_cons cf052_reducible <|
  reducible_in_range_cons cf053_reducible <|
  reducible_in_range_cons cf054_reducible <|
  reducible_in_range_cons cf055_reducible <|
  reducible_in_range_cons cf056_reducible <|
  reducible_in_range_cons cf057_reducible <|
  reducible_in_range_cons cf058_reducible <|
  reducible_in_range_cons cf059_reducible <|
  reducible_in_range_cons cf060_reducible <|
  reducible_in_range_cons cf061_reducible <|
  reducible_in_range_cons cf062_reducible <|
  reducible_in_range_cons cf063_reducible <|
  reducible_in_range_cons cf064_reducible <|
  reducible_in_range_nil 64 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 64 … 95 are C-reducible. -/
theorem reducibleBlock2 : ReducibleInRange 64 96 theConfigs :=
  reducible_in_range_cons cf065_reducible <|
  reducible_in_range_cons cf066_reducible <|
  reducible_in_range_cons cf067_reducible <|
  reducible_in_range_cons cf068_reducible <|
  reducible_in_range_cons cf069_reducible <|
  reducible_in_range_cons cf070_reducible <|
  reducible_in_range_cons cf071_reducible <|
  reducible_in_range_cons cf072_reducible <|
  reducible_in_range_cons cf073_reducible <|
  reducible_in_range_cons cf074_reducible <|
  reducible_in_range_cons cf075_reducible <|
  reducible_in_range_cons cf076_reducible <|
  reducible_in_range_cons cf077_reducible <|
  reducible_in_range_cons cf078_reducible <|
  reducible_in_range_cons cf079_reducible <|
  reducible_in_range_cons cf080_reducible <|
  reducible_in_range_cons cf081_reducible <|
  reducible_in_range_cons cf082_reducible <|
  reducible_in_range_cons cf083_reducible <|
  reducible_in_range_cons cf084_reducible <|
  reducible_in_range_cons cf085_reducible <|
  reducible_in_range_cons cf086_reducible <|
  reducible_in_range_cons cf087_reducible <|
  reducible_in_range_cons cf088_reducible <|
  reducible_in_range_cons cf089_reducible <|
  reducible_in_range_cons cf090_reducible <|
  reducible_in_range_cons cf091_reducible <|
  reducible_in_range_cons cf092_reducible <|
  reducible_in_range_cons cf093_reducible <|
  reducible_in_range_cons cf094_reducible <|
  reducible_in_range_cons cf095_reducible <|
  reducible_in_range_cons cf096_reducible <|
  reducible_in_range_nil 96 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 96 … 127 are C-reducible. -/
theorem reducibleBlock3 : ReducibleInRange 96 128 theConfigs :=
  reducible_in_range_cons cf097_reducible <|
  reducible_in_range_cons cf098_reducible <|
  reducible_in_range_cons cf099_reducible <|
  reducible_in_range_cons cf100_reducible <|
  reducible_in_range_cons cf101_reducible <|
  reducible_in_range_cons cf102_reducible <|
  reducible_in_range_cons cf103_reducible <|
  reducible_in_range_cons cf104_reducible <|
  reducible_in_range_cons cf105_reducible <|
  reducible_in_range_cons cf106_reducible <|
  reducible_in_range_cons cf107_reducible <|
  reducible_in_range_cons cf108_reducible <|
  reducible_in_range_cons cf109_reducible <|
  reducible_in_range_cons cf110_reducible <|
  reducible_in_range_cons cf111_reducible <|
  reducible_in_range_cons cf112_reducible <|
  reducible_in_range_cons cf113_reducible <|
  reducible_in_range_cons cf114_reducible <|
  reducible_in_range_cons cf115_reducible <|
  reducible_in_range_cons cf116_reducible <|
  reducible_in_range_cons cf117_reducible <|
  reducible_in_range_cons cf118_reducible <|
  reducible_in_range_cons cf119_reducible <|
  reducible_in_range_cons cf120_reducible <|
  reducible_in_range_cons cf121_reducible <|
  reducible_in_range_cons cf122_reducible <|
  reducible_in_range_cons cf123_reducible <|
  reducible_in_range_cons cf124_reducible <|
  reducible_in_range_cons cf125_reducible <|
  reducible_in_range_cons cf126_reducible <|
  reducible_in_range_cons cf127_reducible <|
  reducible_in_range_cons cf128_reducible <|
  reducible_in_range_nil 128 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 128 … 159 are C-reducible. -/
theorem reducibleBlock4 : ReducibleInRange 128 160 theConfigs :=
  reducible_in_range_cons cf129_reducible <|
  reducible_in_range_cons cf130_reducible <|
  reducible_in_range_cons cf131_reducible <|
  reducible_in_range_cons cf132_reducible <|
  reducible_in_range_cons cf133_reducible <|
  reducible_in_range_cons cf134_reducible <|
  reducible_in_range_cons cf135_reducible <|
  reducible_in_range_cons cf136_reducible <|
  reducible_in_range_cons cf137_reducible <|
  reducible_in_range_cons cf138_reducible <|
  reducible_in_range_cons cf139_reducible <|
  reducible_in_range_cons cf140_reducible <|
  reducible_in_range_cons cf141_reducible <|
  reducible_in_range_cons cf142_reducible <|
  reducible_in_range_cons cf143_reducible <|
  reducible_in_range_cons cf144_reducible <|
  reducible_in_range_cons cf145_reducible <|
  reducible_in_range_cons cf146_reducible <|
  reducible_in_range_cons cf147_reducible <|
  reducible_in_range_cons cf148_reducible <|
  reducible_in_range_cons cf149_reducible <|
  reducible_in_range_cons cf150_reducible <|
  reducible_in_range_cons cf151_reducible <|
  reducible_in_range_cons cf152_reducible <|
  reducible_in_range_cons cf153_reducible <|
  reducible_in_range_cons cf154_reducible <|
  reducible_in_range_cons cf155_reducible <|
  reducible_in_range_cons cf156_reducible <|
  reducible_in_range_cons cf157_reducible <|
  reducible_in_range_cons cf158_reducible <|
  reducible_in_range_cons cf159_reducible <|
  reducible_in_range_cons cf160_reducible <|
  reducible_in_range_nil 160 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 160 … 191 are C-reducible. -/
theorem reducibleBlock5 : ReducibleInRange 160 192 theConfigs :=
  reducible_in_range_cons cf161_reducible <|
  reducible_in_range_cons cf162_reducible <|
  reducible_in_range_cons cf163_reducible <|
  reducible_in_range_cons cf164_reducible <|
  reducible_in_range_cons cf165_reducible <|
  reducible_in_range_cons cf166_reducible <|
  reducible_in_range_cons cf167_reducible <|
  reducible_in_range_cons cf168_reducible <|
  reducible_in_range_cons cf169_reducible <|
  reducible_in_range_cons cf170_reducible <|
  reducible_in_range_cons cf171_reducible <|
  reducible_in_range_cons cf172_reducible <|
  reducible_in_range_cons cf173_reducible <|
  reducible_in_range_cons cf174_reducible <|
  reducible_in_range_cons cf175_reducible <|
  reducible_in_range_cons cf176_reducible <|
  reducible_in_range_cons cf177_reducible <|
  reducible_in_range_cons cf178_reducible <|
  reducible_in_range_cons cf179_reducible <|
  reducible_in_range_cons cf180_reducible <|
  reducible_in_range_cons cf181_reducible <|
  reducible_in_range_cons cf182_reducible <|
  reducible_in_range_cons cf183_reducible <|
  reducible_in_range_cons cf184_reducible <|
  reducible_in_range_cons cf185_reducible <|
  reducible_in_range_cons cf186_reducible <|
  reducible_in_range_cons cf187_reducible <|
  reducible_in_range_cons cf188_reducible <|
  reducible_in_range_cons cf189_reducible <|
  reducible_in_range_cons cf190_reducible <|
  reducible_in_range_cons cf191_reducible <|
  reducible_in_range_cons cf192_reducible <|
  reducible_in_range_nil 192 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 192 … 223 are C-reducible. -/
theorem reducibleBlock6 : ReducibleInRange 192 224 theConfigs :=
  reducible_in_range_cons cf193_reducible <|
  reducible_in_range_cons cf194_reducible <|
  reducible_in_range_cons cf195_reducible <|
  reducible_in_range_cons cf196_reducible <|
  reducible_in_range_cons cf197_reducible <|
  reducible_in_range_cons cf198_reducible <|
  reducible_in_range_cons cf199_reducible <|
  reducible_in_range_cons cf200_reducible <|
  reducible_in_range_cons cf201_reducible <|
  reducible_in_range_cons cf202_reducible <|
  reducible_in_range_cons cf203_reducible <|
  reducible_in_range_cons cf204_reducible <|
  reducible_in_range_cons cf205_reducible <|
  reducible_in_range_cons cf206_reducible <|
  reducible_in_range_cons cf207_reducible <|
  reducible_in_range_cons cf208_reducible <|
  reducible_in_range_cons cf209_reducible <|
  reducible_in_range_cons cf210_reducible <|
  reducible_in_range_cons cf211_reducible <|
  reducible_in_range_cons cf212_reducible <|
  reducible_in_range_cons cf213_reducible <|
  reducible_in_range_cons cf214_reducible <|
  reducible_in_range_cons cf215_reducible <|
  reducible_in_range_cons cf216_reducible <|
  reducible_in_range_cons cf217_reducible <|
  reducible_in_range_cons cf218_reducible <|
  reducible_in_range_cons cf219_reducible <|
  reducible_in_range_cons cf220_reducible <|
  reducible_in_range_cons cf221_reducible <|
  reducible_in_range_cons cf222_reducible <|
  reducible_in_range_cons cf223_reducible <|
  reducible_in_range_cons cf224_reducible <|
  reducible_in_range_nil 224 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 224 … 255 are C-reducible. -/
theorem reducibleBlock7 : ReducibleInRange 224 256 theConfigs :=
  reducible_in_range_cons cf225_reducible <|
  reducible_in_range_cons cf226_reducible <|
  reducible_in_range_cons cf227_reducible <|
  reducible_in_range_cons cf228_reducible <|
  reducible_in_range_cons cf229_reducible <|
  reducible_in_range_cons cf230_reducible <|
  reducible_in_range_cons cf231_reducible <|
  reducible_in_range_cons cf232_reducible <|
  reducible_in_range_cons cf233_reducible <|
  reducible_in_range_cons cf234_reducible <|
  reducible_in_range_cons cf235_reducible <|
  reducible_in_range_cons cf236_reducible <|
  reducible_in_range_cons cf237_reducible <|
  reducible_in_range_cons cf238_reducible <|
  reducible_in_range_cons cf239_reducible <|
  reducible_in_range_cons cf240_reducible <|
  reducible_in_range_cons cf241_reducible <|
  reducible_in_range_cons cf242_reducible <|
  reducible_in_range_cons cf243_reducible <|
  reducible_in_range_cons cf244_reducible <|
  reducible_in_range_cons cf245_reducible <|
  reducible_in_range_cons cf246_reducible <|
  reducible_in_range_cons cf247_reducible <|
  reducible_in_range_cons cf248_reducible <|
  reducible_in_range_cons cf249_reducible <|
  reducible_in_range_cons cf250_reducible <|
  reducible_in_range_cons cf251_reducible <|
  reducible_in_range_cons cf252_reducible <|
  reducible_in_range_cons cf253_reducible <|
  reducible_in_range_cons cf254_reducible <|
  reducible_in_range_cons cf255_reducible <|
  reducible_in_range_cons cf256_reducible <|
  reducible_in_range_nil 256 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 256 … 287 are C-reducible. -/
theorem reducibleBlock8 : ReducibleInRange 256 288 theConfigs :=
  reducible_in_range_cons cf257_reducible <|
  reducible_in_range_cons cf258_reducible <|
  reducible_in_range_cons cf259_reducible <|
  reducible_in_range_cons cf260_reducible <|
  reducible_in_range_cons cf261_reducible <|
  reducible_in_range_cons cf262_reducible <|
  reducible_in_range_cons cf263_reducible <|
  reducible_in_range_cons cf264_reducible <|
  reducible_in_range_cons cf265_reducible <|
  reducible_in_range_cons cf266_reducible <|
  reducible_in_range_cons cf267_reducible <|
  reducible_in_range_cons cf268_reducible <|
  reducible_in_range_cons cf269_reducible <|
  reducible_in_range_cons cf270_reducible <|
  reducible_in_range_cons cf271_reducible <|
  reducible_in_range_cons cf272_reducible <|
  reducible_in_range_cons cf273_reducible <|
  reducible_in_range_cons cf274_reducible <|
  reducible_in_range_cons cf275_reducible <|
  reducible_in_range_cons cf276_reducible <|
  reducible_in_range_cons cf277_reducible <|
  reducible_in_range_cons cf278_reducible <|
  reducible_in_range_cons cf279_reducible <|
  reducible_in_range_cons cf280_reducible <|
  reducible_in_range_cons cf281_reducible <|
  reducible_in_range_cons cf282_reducible <|
  reducible_in_range_cons cf283_reducible <|
  reducible_in_range_cons cf284_reducible <|
  reducible_in_range_cons cf285_reducible <|
  reducible_in_range_cons cf286_reducible <|
  reducible_in_range_cons cf287_reducible <|
  reducible_in_range_cons cf288_reducible <|
  reducible_in_range_nil 288 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 288 … 319 are C-reducible. -/
theorem reducibleBlock9 : ReducibleInRange 288 320 theConfigs :=
  reducible_in_range_cons cf289_reducible <|
  reducible_in_range_cons cf290_reducible <|
  reducible_in_range_cons cf291_reducible <|
  reducible_in_range_cons cf292_reducible <|
  reducible_in_range_cons cf293_reducible <|
  reducible_in_range_cons cf294_reducible <|
  reducible_in_range_cons cf295_reducible <|
  reducible_in_range_cons cf296_reducible <|
  reducible_in_range_cons cf297_reducible <|
  reducible_in_range_cons cf298_reducible <|
  reducible_in_range_cons cf299_reducible <|
  reducible_in_range_cons cf300_reducible <|
  reducible_in_range_cons cf301_reducible <|
  reducible_in_range_cons cf302_reducible <|
  reducible_in_range_cons cf303_reducible <|
  reducible_in_range_cons cf304_reducible <|
  reducible_in_range_cons cf305_reducible <|
  reducible_in_range_cons cf306_reducible <|
  reducible_in_range_cons cf307_reducible <|
  reducible_in_range_cons cf308_reducible <|
  reducible_in_range_cons cf309_reducible <|
  reducible_in_range_cons cf310_reducible <|
  reducible_in_range_cons cf311_reducible <|
  reducible_in_range_cons cf312_reducible <|
  reducible_in_range_cons cf313_reducible <|
  reducible_in_range_cons cf314_reducible <|
  reducible_in_range_cons cf315_reducible <|
  reducible_in_range_cons cf316_reducible <|
  reducible_in_range_cons cf317_reducible <|
  reducible_in_range_cons cf318_reducible <|
  reducible_in_range_cons cf319_reducible <|
  reducible_in_range_cons cf320_reducible <|
  reducible_in_range_nil 320 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 320 … 351 are C-reducible. -/
theorem reducibleBlock10 : ReducibleInRange 320 352 theConfigs :=
  reducible_in_range_cons cf321_reducible <|
  reducible_in_range_cons cf322_reducible <|
  reducible_in_range_cons cf323_reducible <|
  reducible_in_range_cons cf324_reducible <|
  reducible_in_range_cons cf325_reducible <|
  reducible_in_range_cons cf326_reducible <|
  reducible_in_range_cons cf327_reducible <|
  reducible_in_range_cons cf328_reducible <|
  reducible_in_range_cons cf329_reducible <|
  reducible_in_range_cons cf330_reducible <|
  reducible_in_range_cons cf331_reducible <|
  reducible_in_range_cons cf332_reducible <|
  reducible_in_range_cons cf333_reducible <|
  reducible_in_range_cons cf334_reducible <|
  reducible_in_range_cons cf335_reducible <|
  reducible_in_range_cons cf336_reducible <|
  reducible_in_range_cons cf337_reducible <|
  reducible_in_range_cons cf338_reducible <|
  reducible_in_range_cons cf339_reducible <|
  reducible_in_range_cons cf340_reducible <|
  reducible_in_range_cons cf341_reducible <|
  reducible_in_range_cons cf342_reducible <|
  reducible_in_range_cons cf343_reducible <|
  reducible_in_range_cons cf344_reducible <|
  reducible_in_range_cons cf345_reducible <|
  reducible_in_range_cons cf346_reducible <|
  reducible_in_range_cons cf347_reducible <|
  reducible_in_range_cons cf348_reducible <|
  reducible_in_range_cons cf349_reducible <|
  reducible_in_range_cons cf350_reducible <|
  reducible_in_range_cons cf351_reducible <|
  reducible_in_range_cons cf352_reducible <|
  reducible_in_range_nil 352 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 352 … 383 are C-reducible. -/
theorem reducibleBlock11 : ReducibleInRange 352 384 theConfigs :=
  reducible_in_range_cons cf353_reducible <|
  reducible_in_range_cons cf354_reducible <|
  reducible_in_range_cons cf355_reducible <|
  reducible_in_range_cons cf356_reducible <|
  reducible_in_range_cons cf357_reducible <|
  reducible_in_range_cons cf358_reducible <|
  reducible_in_range_cons cf359_reducible <|
  reducible_in_range_cons cf360_reducible <|
  reducible_in_range_cons cf361_reducible <|
  reducible_in_range_cons cf362_reducible <|
  reducible_in_range_cons cf363_reducible <|
  reducible_in_range_cons cf364_reducible <|
  reducible_in_range_cons cf365_reducible <|
  reducible_in_range_cons cf366_reducible <|
  reducible_in_range_cons cf367_reducible <|
  reducible_in_range_cons cf368_reducible <|
  reducible_in_range_cons cf369_reducible <|
  reducible_in_range_cons cf370_reducible <|
  reducible_in_range_cons cf371_reducible <|
  reducible_in_range_cons cf372_reducible <|
  reducible_in_range_cons cf373_reducible <|
  reducible_in_range_cons cf374_reducible <|
  reducible_in_range_cons cf375_reducible <|
  reducible_in_range_cons cf376_reducible <|
  reducible_in_range_cons cf377_reducible <|
  reducible_in_range_cons cf378_reducible <|
  reducible_in_range_cons cf379_reducible <|
  reducible_in_range_cons cf380_reducible <|
  reducible_in_range_cons cf381_reducible <|
  reducible_in_range_cons cf382_reducible <|
  reducible_in_range_cons cf383_reducible <|
  reducible_in_range_cons cf384_reducible <|
  reducible_in_range_nil 384 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 384 … 415 are C-reducible. -/
theorem reducibleBlock12 : ReducibleInRange 384 416 theConfigs :=
  reducible_in_range_cons cf385_reducible <|
  reducible_in_range_cons cf386_reducible <|
  reducible_in_range_cons cf387_reducible <|
  reducible_in_range_cons cf388_reducible <|
  reducible_in_range_cons cf389_reducible <|
  reducible_in_range_cons cf390_reducible <|
  reducible_in_range_cons cf391_reducible <|
  reducible_in_range_cons cf392_reducible <|
  reducible_in_range_cons cf393_reducible <|
  reducible_in_range_cons cf394_reducible <|
  reducible_in_range_cons cf395_reducible <|
  reducible_in_range_cons cf396_reducible <|
  reducible_in_range_cons cf397_reducible <|
  reducible_in_range_cons cf398_reducible <|
  reducible_in_range_cons cf399_reducible <|
  reducible_in_range_cons cf400_reducible <|
  reducible_in_range_cons cf401_reducible <|
  reducible_in_range_cons cf402_reducible <|
  reducible_in_range_cons cf403_reducible <|
  reducible_in_range_cons cf404_reducible <|
  reducible_in_range_cons cf405_reducible <|
  reducible_in_range_cons cf406_reducible <|
  reducible_in_range_cons cf407_reducible <|
  reducible_in_range_cons cf408_reducible <|
  reducible_in_range_cons cf409_reducible <|
  reducible_in_range_cons cf410_reducible <|
  reducible_in_range_cons cf411_reducible <|
  reducible_in_range_cons cf412_reducible <|
  reducible_in_range_cons cf413_reducible <|
  reducible_in_range_cons cf414_reducible <|
  reducible_in_range_cons cf415_reducible <|
  reducible_in_range_cons cf416_reducible <|
  reducible_in_range_nil 416 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 416 … 447 are C-reducible. -/
theorem reducibleBlock13 : ReducibleInRange 416 448 theConfigs :=
  reducible_in_range_cons cf417_reducible <|
  reducible_in_range_cons cf418_reducible <|
  reducible_in_range_cons cf419_reducible <|
  reducible_in_range_cons cf420_reducible <|
  reducible_in_range_cons cf421_reducible <|
  reducible_in_range_cons cf422_reducible <|
  reducible_in_range_cons cf423_reducible <|
  reducible_in_range_cons cf424_reducible <|
  reducible_in_range_cons cf425_reducible <|
  reducible_in_range_cons cf426_reducible <|
  reducible_in_range_cons cf427_reducible <|
  reducible_in_range_cons cf428_reducible <|
  reducible_in_range_cons cf429_reducible <|
  reducible_in_range_cons cf430_reducible <|
  reducible_in_range_cons cf431_reducible <|
  reducible_in_range_cons cf432_reducible <|
  reducible_in_range_cons cf433_reducible <|
  reducible_in_range_cons cf434_reducible <|
  reducible_in_range_cons cf435_reducible <|
  reducible_in_range_cons cf436_reducible <|
  reducible_in_range_cons cf437_reducible <|
  reducible_in_range_cons cf438_reducible <|
  reducible_in_range_cons cf439_reducible <|
  reducible_in_range_cons cf440_reducible <|
  reducible_in_range_cons cf441_reducible <|
  reducible_in_range_cons cf442_reducible <|
  reducible_in_range_cons cf443_reducible <|
  reducible_in_range_cons cf444_reducible <|
  reducible_in_range_cons cf445_reducible <|
  reducible_in_range_cons cf446_reducible <|
  reducible_in_range_cons cf447_reducible <|
  reducible_in_range_cons cf448_reducible <|
  reducible_in_range_nil 448 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 448 … 479 are C-reducible. -/
theorem reducibleBlock14 : ReducibleInRange 448 480 theConfigs :=
  reducible_in_range_cons cf449_reducible <|
  reducible_in_range_cons cf450_reducible <|
  reducible_in_range_cons cf451_reducible <|
  reducible_in_range_cons cf452_reducible <|
  reducible_in_range_cons cf453_reducible <|
  reducible_in_range_cons cf454_reducible <|
  reducible_in_range_cons cf455_reducible <|
  reducible_in_range_cons cf456_reducible <|
  reducible_in_range_cons cf457_reducible <|
  reducible_in_range_cons cf458_reducible <|
  reducible_in_range_cons cf459_reducible <|
  reducible_in_range_cons cf460_reducible <|
  reducible_in_range_cons cf461_reducible <|
  reducible_in_range_cons cf462_reducible <|
  reducible_in_range_cons cf463_reducible <|
  reducible_in_range_cons cf464_reducible <|
  reducible_in_range_cons cf465_reducible <|
  reducible_in_range_cons cf466_reducible <|
  reducible_in_range_cons cf467_reducible <|
  reducible_in_range_cons cf468_reducible <|
  reducible_in_range_cons cf469_reducible <|
  reducible_in_range_cons cf470_reducible <|
  reducible_in_range_cons cf471_reducible <|
  reducible_in_range_cons cf472_reducible <|
  reducible_in_range_cons cf473_reducible <|
  reducible_in_range_cons cf474_reducible <|
  reducible_in_range_cons cf475_reducible <|
  reducible_in_range_cons cf476_reducible <|
  reducible_in_range_cons cf477_reducible <|
  reducible_in_range_cons cf478_reducible <|
  reducible_in_range_cons cf479_reducible <|
  reducible_in_range_cons cf480_reducible <|
  reducible_in_range_nil 480 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 480 … 511 are C-reducible. -/
theorem reducibleBlock15 : ReducibleInRange 480 512 theConfigs :=
  reducible_in_range_cons cf481_reducible <|
  reducible_in_range_cons cf482_reducible <|
  reducible_in_range_cons cf483_reducible <|
  reducible_in_range_cons cf484_reducible <|
  reducible_in_range_cons cf485_reducible <|
  reducible_in_range_cons cf486_reducible <|
  reducible_in_range_cons cf487_reducible <|
  reducible_in_range_cons cf488_reducible <|
  reducible_in_range_cons cf489_reducible <|
  reducible_in_range_cons cf490_reducible <|
  reducible_in_range_cons cf491_reducible <|
  reducible_in_range_cons cf492_reducible <|
  reducible_in_range_cons cf493_reducible <|
  reducible_in_range_cons cf494_reducible <|
  reducible_in_range_cons cf495_reducible <|
  reducible_in_range_cons cf496_reducible <|
  reducible_in_range_cons cf497_reducible <|
  reducible_in_range_cons cf498_reducible <|
  reducible_in_range_cons cf499_reducible <|
  reducible_in_range_cons cf500_reducible <|
  reducible_in_range_cons cf501_reducible <|
  reducible_in_range_cons cf502_reducible <|
  reducible_in_range_cons cf503_reducible <|
  reducible_in_range_cons cf504_reducible <|
  reducible_in_range_cons cf505_reducible <|
  reducible_in_range_cons cf506_reducible <|
  reducible_in_range_cons cf507_reducible <|
  reducible_in_range_cons cf508_reducible <|
  reducible_in_range_cons cf509_reducible <|
  reducible_in_range_cons cf510_reducible <|
  reducible_in_range_cons cf511_reducible <|
  reducible_in_range_cons cf512_reducible <|
  reducible_in_range_nil 512 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 512 … 543 are C-reducible. -/
theorem reducibleBlock16 : ReducibleInRange 512 544 theConfigs :=
  reducible_in_range_cons cf513_reducible <|
  reducible_in_range_cons cf514_reducible <|
  reducible_in_range_cons cf515_reducible <|
  reducible_in_range_cons cf516_reducible <|
  reducible_in_range_cons cf517_reducible <|
  reducible_in_range_cons cf518_reducible <|
  reducible_in_range_cons cf519_reducible <|
  reducible_in_range_cons cf520_reducible <|
  reducible_in_range_cons cf521_reducible <|
  reducible_in_range_cons cf522_reducible <|
  reducible_in_range_cons cf523_reducible <|
  reducible_in_range_cons cf524_reducible <|
  reducible_in_range_cons cf525_reducible <|
  reducible_in_range_cons cf526_reducible <|
  reducible_in_range_cons cf527_reducible <|
  reducible_in_range_cons cf528_reducible <|
  reducible_in_range_cons cf529_reducible <|
  reducible_in_range_cons cf530_reducible <|
  reducible_in_range_cons cf531_reducible <|
  reducible_in_range_cons cf532_reducible <|
  reducible_in_range_cons cf533_reducible <|
  reducible_in_range_cons cf534_reducible <|
  reducible_in_range_cons cf535_reducible <|
  reducible_in_range_cons cf536_reducible <|
  reducible_in_range_cons cf537_reducible <|
  reducible_in_range_cons cf538_reducible <|
  reducible_in_range_cons cf539_reducible <|
  reducible_in_range_cons cf540_reducible <|
  reducible_in_range_cons cf541_reducible <|
  reducible_in_range_cons cf542_reducible <|
  reducible_in_range_cons cf543_reducible <|
  reducible_in_range_cons cf544_reducible <|
  reducible_in_range_nil 544 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 544 … 575 are C-reducible. -/
theorem reducibleBlock17 : ReducibleInRange 544 576 theConfigs :=
  reducible_in_range_cons cf545_reducible <|
  reducible_in_range_cons cf546_reducible <|
  reducible_in_range_cons cf547_reducible <|
  reducible_in_range_cons cf548_reducible <|
  reducible_in_range_cons cf549_reducible <|
  reducible_in_range_cons cf550_reducible <|
  reducible_in_range_cons cf551_reducible <|
  reducible_in_range_cons cf552_reducible <|
  reducible_in_range_cons cf553_reducible <|
  reducible_in_range_cons cf554_reducible <|
  reducible_in_range_cons cf555_reducible <|
  reducible_in_range_cons cf556_reducible <|
  reducible_in_range_cons cf557_reducible <|
  reducible_in_range_cons cf558_reducible <|
  reducible_in_range_cons cf559_reducible <|
  reducible_in_range_cons cf560_reducible <|
  reducible_in_range_cons cf561_reducible <|
  reducible_in_range_cons cf562_reducible <|
  reducible_in_range_cons cf563_reducible <|
  reducible_in_range_cons cf564_reducible <|
  reducible_in_range_cons cf565_reducible <|
  reducible_in_range_cons cf566_reducible <|
  reducible_in_range_cons cf567_reducible <|
  reducible_in_range_cons cf568_reducible <|
  reducible_in_range_cons cf569_reducible <|
  reducible_in_range_cons cf570_reducible <|
  reducible_in_range_cons cf571_reducible <|
  reducible_in_range_cons cf572_reducible <|
  reducible_in_range_cons cf573_reducible <|
  reducible_in_range_cons cf574_reducible <|
  reducible_in_range_cons cf575_reducible <|
  reducible_in_range_cons cf576_reducible <|
  reducible_in_range_nil 576 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 576 … 607 are C-reducible. -/
theorem reducibleBlock18 : ReducibleInRange 576 608 theConfigs :=
  reducible_in_range_cons cf577_reducible <|
  reducible_in_range_cons cf578_reducible <|
  reducible_in_range_cons cf579_reducible <|
  reducible_in_range_cons cf580_reducible <|
  reducible_in_range_cons cf581_reducible <|
  reducible_in_range_cons cf582_reducible <|
  reducible_in_range_cons cf583_reducible <|
  reducible_in_range_cons cf584_reducible <|
  reducible_in_range_cons cf585_reducible <|
  reducible_in_range_cons cf586_reducible <|
  reducible_in_range_cons cf587_reducible <|
  reducible_in_range_cons cf588_reducible <|
  reducible_in_range_cons cf589_reducible <|
  reducible_in_range_cons cf590_reducible <|
  reducible_in_range_cons cf591_reducible <|
  reducible_in_range_cons cf592_reducible <|
  reducible_in_range_cons cf593_reducible <|
  reducible_in_range_cons cf594_reducible <|
  reducible_in_range_cons cf595_reducible <|
  reducible_in_range_cons cf596_reducible <|
  reducible_in_range_cons cf597_reducible <|
  reducible_in_range_cons cf598_reducible <|
  reducible_in_range_cons cf599_reducible <|
  reducible_in_range_cons cf600_reducible <|
  reducible_in_range_cons cf601_reducible <|
  reducible_in_range_cons cf602_reducible <|
  reducible_in_range_cons cf603_reducible <|
  reducible_in_range_cons cf604_reducible <|
  reducible_in_range_cons cf605_reducible <|
  reducible_in_range_cons cf606_reducible <|
  reducible_in_range_cons cf607_reducible <|
  reducible_in_range_cons cf608_reducible <|
  reducible_in_range_nil 608 theConfigs

set_option maxRecDepth 8000 in
/-- The configurations of indices 608 … 632 are C-reducible. -/
theorem reducibleBlock19 : ReducibleInRange 608 633 theConfigs :=
  reducible_in_range_cons cf609_reducible <|
  reducible_in_range_cons cf610_reducible <|
  reducible_in_range_cons cf611_reducible <|
  reducible_in_range_cons cf612_reducible <|
  reducible_in_range_cons cf613_reducible <|
  reducible_in_range_cons cf614_reducible <|
  reducible_in_range_cons cf615_reducible <|
  reducible_in_range_cons cf616_reducible <|
  reducible_in_range_cons cf617_reducible <|
  reducible_in_range_cons cf618_reducible <|
  reducible_in_range_cons cf619_reducible <|
  reducible_in_range_cons cf620_reducible <|
  reducible_in_range_cons cf621_reducible <|
  reducible_in_range_cons cf622_reducible <|
  reducible_in_range_cons cf623_reducible <|
  reducible_in_range_cons cf624_reducible <|
  reducible_in_range_cons cf625_reducible <|
  reducible_in_range_cons cf626_reducible <|
  reducible_in_range_cons cf627_reducible <|
  reducible_in_range_cons cf628_reducible <|
  reducible_in_range_cons cf629_reducible <|
  reducible_in_range_cons cf630_reducible <|
  reducible_in_range_cons cf631_reducible <|
  reducible_in_range_cons cf632_reducible <|
  reducible_in_range_cons cf633_reducible <|
  reducible_in_range_nil 633 theConfigs

/-- math-comp `the_reducibility : reducibility`: all the configurations of `theConfigs` are
C-reducible. -/
theorem theReducibility : ReducibleInRange 0 633 theConfigs :=
  cat_reducible_range reducibleBlock0 <|
  cat_reducible_range reducibleBlock1 <|
  cat_reducible_range reducibleBlock2 <|
  cat_reducible_range reducibleBlock3 <|
  cat_reducible_range reducibleBlock4 <|
  cat_reducible_range reducibleBlock5 <|
  cat_reducible_range reducibleBlock6 <|
  cat_reducible_range reducibleBlock7 <|
  cat_reducible_range reducibleBlock8 <|
  cat_reducible_range reducibleBlock9 <|
  cat_reducible_range reducibleBlock10 <|
  cat_reducible_range reducibleBlock11 <|
  cat_reducible_range reducibleBlock12 <|
  cat_reducible_range reducibleBlock13 <|
  cat_reducible_range reducibleBlock14 <|
  cat_reducible_range reducibleBlock15 <|
  cat_reducible_range reducibleBlock16 <|
  cat_reducible_range reducibleBlock17 <|
  cat_reducible_range reducibleBlock18 <|
  reducibleBlock19

end FourColor
