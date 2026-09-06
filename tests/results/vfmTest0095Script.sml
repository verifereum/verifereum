Theory vfmTest0095[no_sig_docs]
Ancestors vfmTestDefs0095
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0095_0.nsv", "result0095_1.nsv"];
val thyn = "vfmTestDefs0095";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
