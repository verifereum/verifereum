Theory vfmTest1874[no_sig_docs]
Ancestors vfmTestDefs1874
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1874_0.nsv", "result1874_1.nsv"];
val thyn = "vfmTestDefs1874";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
