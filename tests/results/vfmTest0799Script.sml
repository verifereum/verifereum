Theory vfmTest0799[no_sig_docs]
Ancestors vfmTestDefs0799
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0799_0.nsv", "result0799_1.nsv", "result0799_2.nsv", "result0799_3.nsv"];
val thyn = "vfmTestDefs0799";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
