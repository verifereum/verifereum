Theory vfmTest0430[no_sig_docs]
Ancestors vfmTestDefs0430
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0430_0.nsv", "result0430_1.nsv", "result0430_2.nsv", "result0430_3.nsv", "result0430_4.nsv", "result0430_5.nsv", "result0430_6.nsv", "result0430_7.nsv", "result0430_8.nsv", "result0430_9.nsv", "result0430_10.nsv"];
val thyn = "vfmTestDefs0430";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
