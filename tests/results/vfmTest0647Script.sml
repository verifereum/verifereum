Theory vfmTest0647[no_sig_docs]
Ancestors vfmTestDefs0647
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0647_0.nsv", "result0647_1.nsv", "result0647_2.nsv", "result0647_3.nsv"];
val thyn = "vfmTestDefs0647";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
