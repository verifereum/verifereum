Theory vfmTest0514[no_sig_docs]
Ancestors vfmTestDefs0514
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0514_0.nsv", "result0514_1.nsv"];
val thyn = "vfmTestDefs0514";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
