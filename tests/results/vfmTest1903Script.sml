Theory vfmTest1903[no_sig_docs]
Ancestors vfmTestDefs1903
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1903_0.nsv"];
val thyn = "vfmTestDefs1903";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
