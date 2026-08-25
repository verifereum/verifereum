Theory vfmTest1433[no_sig_docs]
Ancestors vfmTestDefs1433
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1433_0.nsv"];
val thyn = "vfmTestDefs1433";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
