Theory vfmTest0193[no_sig_docs]
Ancestors vfmTestDefs0193
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0193_0.nsv", "result0193_1.nsv", "result0193_2.nsv", "result0193_3.nsv"];
val thyn = "vfmTestDefs0193";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
