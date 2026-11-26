Theory vfmTest0428[no_sig_docs]
Ancestors vfmTestDefs0428
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0428_0.nsv", "result0428_1.nsv", "result0428_2.nsv", "result0428_3.nsv", "result0428_4.nsv", "result0428_5.nsv", "result0428_6.nsv", "result0428_7.nsv", "result0428_8.nsv", "result0428_9.nsv", "result0428_10.nsv", "result0428_11.nsv", "result0428_12.nsv", "result0428_13.nsv", "result0428_14.nsv", "result0428_15.nsv", "result0428_16.nsv", "result0428_17.nsv", "result0428_18.nsv", "result0428_19.nsv", "result0428_20.nsv", "result0428_21.nsv"];
val thyn = "vfmTestDefs0428";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
