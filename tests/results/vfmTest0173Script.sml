Theory vfmTest0173[no_sig_docs]
Ancestors vfmTestDefs0173
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0173_0.nsv", "result0173_1.nsv", "result0173_2.nsv", "result0173_3.nsv", "result0173_4.nsv", "result0173_5.nsv", "result0173_6.nsv", "result0173_7.nsv", "result0173_8.nsv", "result0173_9.nsv"];
val thyn = "vfmTestDefs0173";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
