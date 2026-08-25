Theory vfmTest0124[no_sig_docs]
Ancestors vfmTestDefs0124
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0124_0.nsv", "result0124_1.nsv", "result0124_2.nsv", "result0124_3.nsv"];
val thyn = "vfmTestDefs0124";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
