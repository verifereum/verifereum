Theory vfmTest0942[no_sig_docs]
Ancestors vfmTestDefs0942
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0942_0.nsv"];
val thyn = "vfmTestDefs0942";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
