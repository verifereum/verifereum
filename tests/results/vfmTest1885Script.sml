Theory vfmTest1885[no_sig_docs]
Ancestors vfmTestDefs1885
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1885_0.nsv"];
val thyn = "vfmTestDefs1885";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
