Theory vfmTest0355[no_sig_docs]
Ancestors vfmTestDefs0355
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0355_0.nsv", "result0355_1.nsv", "result0355_2.nsv", "result0355_3.nsv", "result0355_4.nsv", "result0355_5.nsv", "result0355_6.nsv", "result0355_7.nsv", "result0355_8.nsv", "result0355_9.nsv", "result0355_10.nsv", "result0355_11.nsv"];
val thyn = "vfmTestDefs0355";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
