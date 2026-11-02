Theory vfmTest1087[no_sig_docs]
Ancestors vfmTestDefs1087
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1087_0.nsv", "result1087_1.nsv", "result1087_2.nsv", "result1087_3.nsv", "result1087_4.nsv", "result1087_5.nsv", "result1087_6.nsv", "result1087_7.nsv", "result1087_8.nsv", "result1087_9.nsv", "result1087_10.nsv", "result1087_11.nsv", "result1087_12.nsv", "result1087_13.nsv", "result1087_14.nsv", "result1087_15.nsv"];
val thyn = "vfmTestDefs1087";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
