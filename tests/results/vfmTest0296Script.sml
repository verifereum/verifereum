Theory vfmTest0296[no_sig_docs]
Ancestors vfmTestDefs0296
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0296_0.nsv", "result0296_1.nsv"];
val thyn = "vfmTestDefs0296";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
