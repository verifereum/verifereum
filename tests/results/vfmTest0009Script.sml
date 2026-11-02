Theory vfmTest0009[no_sig_docs]
Ancestors vfmTestDefs0009
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0009_0.nsv", "result0009_1.nsv"];
val thyn = "vfmTestDefs0009";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
