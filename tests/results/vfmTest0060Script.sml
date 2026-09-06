Theory vfmTest0060[no_sig_docs]
Ancestors vfmTestDefs0060
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0060_0.nsv", "result0060_1.nsv", "result0060_2.nsv", "result0060_3.nsv", "result0060_4.nsv", "result0060_5.nsv", "result0060_6.nsv", "result0060_7.nsv", "result0060_8.nsv", "result0060_9.nsv", "result0060_10.nsv", "result0060_11.nsv", "result0060_12.nsv", "result0060_13.nsv", "result0060_14.nsv", "result0060_15.nsv", "result0060_16.nsv", "result0060_17.nsv", "result0060_18.nsv", "result0060_19.nsv", "result0060_20.nsv", "result0060_21.nsv", "result0060_22.nsv", "result0060_23.nsv"];
val thyn = "vfmTestDefs0060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
