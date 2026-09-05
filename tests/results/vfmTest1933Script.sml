Theory vfmTest1933[no_sig_docs]
Ancestors vfmTestDefs1933
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1933_0.nsv"];
val thyn = "vfmTestDefs1933";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
