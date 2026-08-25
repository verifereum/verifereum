Theory vfmTest1339[no_sig_docs]
Ancestors vfmTestDefs1339
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1339_0.nsv"];
val thyn = "vfmTestDefs1339";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
