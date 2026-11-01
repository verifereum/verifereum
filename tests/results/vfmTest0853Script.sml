Theory vfmTest0853[no_sig_docs]
Ancestors vfmTestDefs0853
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0853_0.nsv", "result0853_1.nsv"];
val thyn = "vfmTestDefs0853";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
