Theory vfmTest0153[no_sig_docs]
Ancestors vfmTestDefs0153
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0153_0.nsv", "result0153_1.nsv", "result0153_2.nsv"];
val thyn = "vfmTestDefs0153";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
