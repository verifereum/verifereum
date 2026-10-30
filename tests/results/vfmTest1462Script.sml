Theory vfmTest1462[no_sig_docs]
Ancestors vfmTestDefs1462
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1462_0.nsv", "result1462_1.nsv", "result1462_2.nsv", "result1462_3.nsv", "result1462_4.nsv", "result1462_5.nsv"];
val thyn = "vfmTestDefs1462";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
