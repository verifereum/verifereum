Theory vfmTest0138[no_sig_docs]
Ancestors vfmTestDefs0138
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0138_0.nsv", "result0138_1.nsv", "result0138_2.nsv", "result0138_3.nsv"];
val thyn = "vfmTestDefs0138";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
