Theory vfmTest0923[no_sig_docs]
Ancestors vfmTestDefs0923
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0923_0.nsv", "result0923_1.nsv", "result0923_2.nsv", "result0923_3.nsv", "result0923_4.nsv", "result0923_5.nsv"];
val thyn = "vfmTestDefs0923";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
