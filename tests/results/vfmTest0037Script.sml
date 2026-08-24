Theory vfmTest0037[no_sig_docs]
Ancestors vfmTestDefs0037
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0037_0.nsv"];
val thyn = "vfmTestDefs0037";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
