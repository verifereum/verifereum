Theory vfmTest0885[no_sig_docs]
Ancestors vfmTestDefs0885
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0885_0.nsv", "result0885_1.nsv"];
val thyn = "vfmTestDefs0885";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
