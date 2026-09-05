Theory vfmTest0241[no_sig_docs]
Ancestors vfmTestDefs0241
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0241_0.nsv", "result0241_1.nsv", "result0241_2.nsv", "result0241_3.nsv", "result0241_4.nsv", "result0241_5.nsv", "result0241_6.nsv", "result0241_7.nsv", "result0241_8.nsv", "result0241_9.nsv", "result0241_10.nsv", "result0241_11.nsv", "result0241_12.nsv", "result0241_13.nsv", "result0241_14.nsv", "result0241_15.nsv", "result0241_16.nsv", "result0241_17.nsv", "result0241_18.nsv", "result0241_19.nsv", "result0241_20.nsv"];
val thyn = "vfmTestDefs0241";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
