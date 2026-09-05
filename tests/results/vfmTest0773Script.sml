Theory vfmTest0773[no_sig_docs]
Ancestors vfmTestDefs0773
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0773_0.nsv", "result0773_1.nsv", "result0773_2.nsv", "result0773_3.nsv", "result0773_4.nsv", "result0773_5.nsv", "result0773_6.nsv", "result0773_7.nsv", "result0773_8.nsv", "result0773_9.nsv", "result0773_10.nsv", "result0773_11.nsv", "result0773_12.nsv", "result0773_13.nsv", "result0773_14.nsv", "result0773_15.nsv", "result0773_16.nsv", "result0773_17.nsv", "result0773_18.nsv", "result0773_19.nsv"];
val thyn = "vfmTestDefs0773";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
