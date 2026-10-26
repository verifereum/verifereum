Theory vfmTest0610[no_sig_docs]
Ancestors vfmTestDefs0610
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0610_0.nsv"];
val thyn = "vfmTestDefs0610";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
