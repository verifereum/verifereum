Theory vfmTest2084[no_sig_docs]
Ancestors vfmTestDefs2084
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2084_0.nsv", "result2084_1.nsv", "result2084_2.nsv", "result2084_3.nsv", "result2084_4.nsv", "result2084_5.nsv", "result2084_6.nsv", "result2084_7.nsv", "result2084_8.nsv", "result2084_9.nsv", "result2084_10.nsv", "result2084_11.nsv", "result2084_12.nsv", "result2084_13.nsv", "result2084_14.nsv", "result2084_15.nsv", "result2084_16.nsv", "result2084_17.nsv", "result2084_18.nsv", "result2084_19.nsv", "result2084_20.nsv", "result2084_21.nsv", "result2084_22.nsv", "result2084_23.nsv", "result2084_24.nsv", "result2084_25.nsv", "result2084_26.nsv", "result2084_27.nsv", "result2084_28.nsv", "result2084_29.nsv"];
val thyn = "vfmTestDefs2084";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
