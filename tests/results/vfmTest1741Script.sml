Theory vfmTest1741[no_sig_docs]
Ancestors vfmTestDefs1741
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1741_0.nsv", "result1741_1.nsv", "result1741_2.nsv", "result1741_3.nsv"];
val thyn = "vfmTestDefs1741";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
