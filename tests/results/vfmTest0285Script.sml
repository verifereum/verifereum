Theory vfmTest0285[no_sig_docs]
Ancestors vfmTestDefs0285
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0285_0.nsv", "result0285_1.nsv"];
val thyn = "vfmTestDefs0285";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
