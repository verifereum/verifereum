Theory vfmTest0815[no_sig_docs]
Ancestors vfmTestDefs0815
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0815_0.nsv", "result0815_1.nsv", "result0815_2.nsv", "result0815_3.nsv", "result0815_4.nsv", "result0815_5.nsv", "result0815_6.nsv", "result0815_7.nsv", "result0815_8.nsv"];
val thyn = "vfmTestDefs0815";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
