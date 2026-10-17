Theory vfmTest2436[no_sig_docs]
Ancestors vfmTestDefs2436
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2436_0.nsv", "result2436_1.nsv", "result2436_2.nsv", "result2436_3.nsv", "result2436_4.nsv", "result2436_5.nsv", "result2436_6.nsv", "result2436_7.nsv", "result2436_8.nsv", "result2436_9.nsv", "result2436_10.nsv", "result2436_11.nsv", "result2436_12.nsv", "result2436_13.nsv", "result2436_14.nsv", "result2436_15.nsv", "result2436_16.nsv", "result2436_17.nsv", "result2436_18.nsv", "result2436_19.nsv", "result2436_20.nsv", "result2436_21.nsv", "result2436_22.nsv", "result2436_23.nsv", "result2436_24.nsv", "result2436_25.nsv", "result2436_26.nsv", "result2436_27.nsv", "result2436_28.nsv", "result2436_29.nsv", "result2436_30.nsv", "result2436_31.nsv", "result2436_32.nsv", "result2436_33.nsv", "result2436_34.nsv", "result2436_35.nsv"];
val thyn = "vfmTestDefs2436";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
