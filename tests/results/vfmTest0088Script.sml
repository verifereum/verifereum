Theory vfmTest0088[no_sig_docs]
Ancestors vfmTestDefs0088
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0088_0.nsv", "result0088_1.nsv", "result0088_2.nsv", "result0088_3.nsv"];
val thyn = "vfmTestDefs0088";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
