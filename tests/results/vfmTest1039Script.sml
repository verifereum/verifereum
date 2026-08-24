Theory vfmTest1039[no_sig_docs]
Ancestors vfmTestDefs1039
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1039_0.nsv"];
val thyn = "vfmTestDefs1039";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
