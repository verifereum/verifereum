Theory vfmTest0337[no_sig_docs]
Ancestors vfmTestDefs0337
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0337_0.nsv", "result0337_1.nsv"];
val thyn = "vfmTestDefs0337";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
