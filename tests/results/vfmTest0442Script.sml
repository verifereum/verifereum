Theory vfmTest0442[no_sig_docs]
Ancestors vfmTestDefs0442
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0442_0.nsv", "result0442_1.nsv", "result0442_2.nsv", "result0442_3.nsv", "result0442_4.nsv"];
val thyn = "vfmTestDefs0442";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
