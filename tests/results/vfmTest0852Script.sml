Theory vfmTest0852[no_sig_docs]
Ancestors vfmTestDefs0852
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0852_0.nsv", "result0852_1.nsv", "result0852_2.nsv", "result0852_3.nsv", "result0852_4.nsv", "result0852_5.nsv", "result0852_6.nsv", "result0852_7.nsv", "result0852_8.nsv", "result0852_9.nsv", "result0852_10.nsv", "result0852_11.nsv", "result0852_12.nsv", "result0852_13.nsv", "result0852_14.nsv", "result0852_15.nsv", "result0852_16.nsv", "result0852_17.nsv", "result0852_18.nsv", "result0852_19.nsv", "result0852_20.nsv", "result0852_21.nsv"];
val thyn = "vfmTestDefs0852";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
