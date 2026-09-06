Theory vfmTest0107[no_sig_docs]
Ancestors vfmTestDefs0107
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0107_0.nsv", "result0107_1.nsv"];
val thyn = "vfmTestDefs0107";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
