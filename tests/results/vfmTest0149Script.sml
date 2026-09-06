Theory vfmTest0149[no_sig_docs]
Ancestors vfmTestDefs0149
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0149_0.nsv", "result0149_1.nsv", "result0149_2.nsv"];
val thyn = "vfmTestDefs0149";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
