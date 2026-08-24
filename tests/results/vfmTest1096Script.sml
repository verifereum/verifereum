Theory vfmTest1096[no_sig_docs]
Ancestors vfmTestDefs1096
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1096_0.nsv"];
val thyn = "vfmTestDefs1096";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
