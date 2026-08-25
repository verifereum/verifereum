Theory vfmTest1997[no_sig_docs]
Ancestors vfmTestDefs1997
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1997_0.nsv", "result1997_1.nsv", "result1997_2.nsv"];
val thyn = "vfmTestDefs1997";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
