Theory vfmTest0271[no_sig_docs]
Ancestors vfmTestDefs0271
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0271_0.nsv", "result0271_1.nsv", "result0271_2.nsv", "result0271_3.nsv"];
val thyn = "vfmTestDefs0271";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
