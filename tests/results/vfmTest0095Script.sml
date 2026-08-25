Theory vfmTest0095[no_sig_docs]
Ancestors vfmTestDefs0095
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0095_0.nsv", "result0095_1.nsv", "result0095_2.nsv", "result0095_3.nsv", "result0095_4.nsv", "result0095_5.nsv", "result0095_6.nsv", "result0095_7.nsv", "result0095_8.nsv", "result0095_9.nsv", "result0095_10.nsv", "result0095_11.nsv", "result0095_12.nsv", "result0095_13.nsv", "result0095_14.nsv", "result0095_15.nsv", "result0095_16.nsv", "result0095_17.nsv", "result0095_18.nsv", "result0095_19.nsv", "result0095_20.nsv"];
val thyn = "vfmTestDefs0095";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
