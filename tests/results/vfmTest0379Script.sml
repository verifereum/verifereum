Theory vfmTest0379[no_sig_docs]
Ancestors vfmTestDefs0379
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0379_0.nsv"];
val thyn = "vfmTestDefs0379";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
