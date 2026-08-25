Theory vfmTest0103[no_sig_docs]
Ancestors vfmTestDefs0103
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0103_0.nsv", "result0103_1.nsv", "result0103_2.nsv", "result0103_3.nsv"];
val thyn = "vfmTestDefs0103";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
