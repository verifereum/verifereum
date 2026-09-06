Theory vfmTest1992[no_sig_docs]
Ancestors vfmTestDefs1992
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1992_0.nsv", "result1992_1.nsv"];
val thyn = "vfmTestDefs1992";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
