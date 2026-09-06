Theory vfmTest0761[no_sig_docs]
Ancestors vfmTestDefs0761
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0761_0.nsv", "result0761_1.nsv", "result0761_2.nsv", "result0761_3.nsv"];
val thyn = "vfmTestDefs0761";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
