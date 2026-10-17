Theory vfmTest2448[no_sig_docs]
Ancestors vfmTestDefs2448
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2448_0.nsv", "result2448_1.nsv", "result2448_2.nsv", "result2448_3.nsv", "result2448_4.nsv", "result2448_5.nsv", "result2448_6.nsv", "result2448_7.nsv", "result2448_8.nsv", "result2448_9.nsv", "result2448_10.nsv", "result2448_11.nsv", "result2448_12.nsv", "result2448_13.nsv", "result2448_14.nsv", "result2448_15.nsv", "result2448_16.nsv", "result2448_17.nsv", "result2448_18.nsv", "result2448_19.nsv", "result2448_20.nsv", "result2448_21.nsv", "result2448_22.nsv", "result2448_23.nsv", "result2448_24.nsv", "result2448_25.nsv", "result2448_26.nsv", "result2448_27.nsv", "result2448_28.nsv", "result2448_29.nsv", "result2448_30.nsv", "result2448_31.nsv", "result2448_32.nsv", "result2448_33.nsv", "result2448_34.nsv", "result2448_35.nsv", "result2448_36.nsv", "result2448_37.nsv", "result2448_38.nsv", "result2448_39.nsv"];
val thyn = "vfmTestDefs2448";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
