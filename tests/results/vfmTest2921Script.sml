Theory vfmTest2921[no_sig_docs]
Ancestors vfmTestDefs2921
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2921_0.nsv"];
val thyn = "vfmTestDefs2921";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
