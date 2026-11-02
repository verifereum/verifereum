Theory vfmTest0790[no_sig_docs]
Ancestors vfmTestDefs0790
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0790_0.nsv", "result0790_1.nsv", "result0790_2.nsv", "result0790_3.nsv"];
val thyn = "vfmTestDefs0790";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
