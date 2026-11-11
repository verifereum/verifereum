Theory vfmTest0237[no_sig_docs]
Ancestors vfmTestDefs0237
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0237_0.nsv", "result0237_1.nsv", "result0237_2.nsv", "result0237_3.nsv"];
val thyn = "vfmTestDefs0237";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
