Theory vfmTest0136[no_sig_docs]
Ancestors vfmTestDefs0136
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0136_0.nsv", "result0136_1.nsv", "result0136_2.nsv", "result0136_3.nsv", "result0136_4.nsv", "result0136_5.nsv", "result0136_6.nsv", "result0136_7.nsv", "result0136_8.nsv", "result0136_9.nsv", "result0136_10.nsv", "result0136_11.nsv", "result0136_12.nsv", "result0136_13.nsv", "result0136_14.nsv", "result0136_15.nsv"];
val thyn = "vfmTestDefs0136";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
