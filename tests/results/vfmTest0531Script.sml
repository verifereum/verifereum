Theory vfmTest0531[no_sig_docs]
Ancestors vfmTestDefs0531
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0531_0.nsv", "result0531_1.nsv", "result0531_2.nsv", "result0531_3.nsv", "result0531_4.nsv", "result0531_5.nsv", "result0531_6.nsv", "result0531_7.nsv", "result0531_8.nsv", "result0531_9.nsv", "result0531_10.nsv"];
val thyn = "vfmTestDefs0531";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
