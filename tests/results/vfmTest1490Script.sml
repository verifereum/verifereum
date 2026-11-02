Theory vfmTest1490[no_sig_docs]
Ancestors vfmTestDefs1490
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1490_0.nsv", "result1490_1.nsv", "result1490_2.nsv", "result1490_3.nsv", "result1490_4.nsv", "result1490_5.nsv", "result1490_6.nsv", "result1490_7.nsv", "result1490_8.nsv", "result1490_9.nsv", "result1490_10.nsv", "result1490_11.nsv"];
val thyn = "vfmTestDefs1490";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
