Theory vfmTest1017[no_sig_docs]
Ancestors vfmTestDefs1017
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1017_0.nsv", "result1017_1.nsv", "result1017_2.nsv", "result1017_3.nsv", "result1017_4.nsv", "result1017_5.nsv", "result1017_6.nsv", "result1017_7.nsv", "result1017_8.nsv", "result1017_9.nsv", "result1017_10.nsv", "result1017_11.nsv", "result1017_12.nsv", "result1017_13.nsv", "result1017_14.nsv", "result1017_15.nsv", "result1017_16.nsv", "result1017_17.nsv", "result1017_18.nsv", "result1017_19.nsv", "result1017_20.nsv", "result1017_21.nsv", "result1017_22.nsv", "result1017_23.nsv"];
val thyn = "vfmTestDefs1017";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
