Theory vfmTest0711[no_sig_docs]
Ancestors vfmTestDefs0711
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0711_0.nsv", "result0711_1.nsv", "result0711_2.nsv", "result0711_3.nsv", "result0711_4.nsv", "result0711_5.nsv", "result0711_6.nsv", "result0711_7.nsv", "result0711_8.nsv", "result0711_9.nsv", "result0711_10.nsv", "result0711_11.nsv"];
val thyn = "vfmTestDefs0711";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
