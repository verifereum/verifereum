Theory vfmTest0170[no_sig_docs]
Ancestors vfmTestDefs0170
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0170_0.nsv", "result0170_1.nsv", "result0170_2.nsv"];
val thyn = "vfmTestDefs0170";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
