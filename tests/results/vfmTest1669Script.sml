Theory vfmTest1669[no_sig_docs]
Ancestors vfmTestDefs1669
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1669_0.nsv", "result1669_1.nsv", "result1669_2.nsv", "result1669_3.nsv", "result1669_4.nsv", "result1669_5.nsv", "result1669_6.nsv", "result1669_7.nsv", "result1669_8.nsv", "result1669_9.nsv", "result1669_10.nsv", "result1669_11.nsv", "result1669_12.nsv", "result1669_13.nsv", "result1669_14.nsv", "result1669_15.nsv", "result1669_16.nsv", "result1669_17.nsv", "result1669_18.nsv", "result1669_19.nsv"];
val thyn = "vfmTestDefs1669";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
