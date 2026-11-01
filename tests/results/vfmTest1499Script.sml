Theory vfmTest1499[no_sig_docs]
Ancestors vfmTestDefs1499
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1499_0.nsv", "result1499_1.nsv", "result1499_2.nsv", "result1499_3.nsv", "result1499_4.nsv", "result1499_5.nsv"];
val thyn = "vfmTestDefs1499";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
