Theory vfmTest0097[no_sig_docs]
Ancestors vfmTestDefs0097
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0097_0.nsv", "result0097_1.nsv", "result0097_2.nsv", "result0097_3.nsv"];
val thyn = "vfmTestDefs0097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
