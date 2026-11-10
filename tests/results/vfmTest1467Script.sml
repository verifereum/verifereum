Theory vfmTest1467[no_sig_docs]
Ancestors vfmTestDefs1467
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1467_0.nsv", "result1467_1.nsv", "result1467_2.nsv", "result1467_3.nsv", "result1467_4.nsv", "result1467_5.nsv", "result1467_6.nsv", "result1467_7.nsv", "result1467_8.nsv", "result1467_9.nsv", "result1467_10.nsv", "result1467_11.nsv", "result1467_12.nsv", "result1467_13.nsv", "result1467_14.nsv", "result1467_15.nsv", "result1467_16.nsv", "result1467_17.nsv", "result1467_18.nsv", "result1467_19.nsv", "result1467_20.nsv", "result1467_21.nsv", "result1467_22.nsv", "result1467_23.nsv", "result1467_24.nsv", "result1467_25.nsv", "result1467_26.nsv", "result1467_27.nsv", "result1467_28.nsv", "result1467_29.nsv", "result1467_30.nsv", "result1467_31.nsv", "result1467_32.nsv", "result1467_33.nsv"];
val thyn = "vfmTestDefs1467";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
