Theory vfmTest0297[no_sig_docs]
Ancestors vfmTestDefs0297
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0297_0.nsv", "result0297_1.nsv", "result0297_2.nsv", "result0297_3.nsv", "result0297_4.nsv", "result0297_5.nsv"];
val thyn = "vfmTestDefs0297";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
