Theory vfmTest0448[no_sig_docs]
Ancestors vfmTestDefs0448
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0448_0.nsv", "result0448_1.nsv", "result0448_2.nsv"];
val thyn = "vfmTestDefs0448";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
