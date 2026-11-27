Theory vfmTest0353[no_sig_docs]
Ancestors vfmTestDefs0353
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0353_0.nsv", "result0353_1.nsv", "result0353_2.nsv", "result0353_3.nsv", "result0353_4.nsv", "result0353_5.nsv", "result0353_6.nsv", "result0353_7.nsv", "result0353_8.nsv", "result0353_9.nsv", "result0353_10.nsv", "result0353_11.nsv", "result0353_12.nsv", "result0353_13.nsv", "result0353_14.nsv", "result0353_15.nsv", "result0353_16.nsv", "result0353_17.nsv", "result0353_18.nsv", "result0353_19.nsv"];
val thyn = "vfmTestDefs0353";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
