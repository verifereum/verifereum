Theory vfmTest1045[no_sig_docs]
Ancestors vfmTestDefs1045
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1045_0.nsv", "result1045_1.nsv", "result1045_2.nsv", "result1045_3.nsv", "result1045_4.nsv", "result1045_5.nsv", "result1045_6.nsv", "result1045_7.nsv", "result1045_8.nsv", "result1045_9.nsv", "result1045_10.nsv", "result1045_11.nsv", "result1045_12.nsv", "result1045_13.nsv", "result1045_14.nsv", "result1045_15.nsv", "result1045_16.nsv", "result1045_17.nsv", "result1045_18.nsv", "result1045_19.nsv", "result1045_20.nsv", "result1045_21.nsv", "result1045_22.nsv", "result1045_23.nsv", "result1045_24.nsv", "result1045_25.nsv", "result1045_26.nsv", "result1045_27.nsv", "result1045_28.nsv", "result1045_29.nsv", "result1045_30.nsv", "result1045_31.nsv"];
val thyn = "vfmTestDefs1045";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
