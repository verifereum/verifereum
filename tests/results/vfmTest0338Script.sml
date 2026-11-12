Theory vfmTest0338[no_sig_docs]
Ancestors vfmTestDefs0338
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0338_0.nsv", "result0338_1.nsv", "result0338_2.nsv", "result0338_3.nsv", "result0338_4.nsv", "result0338_5.nsv", "result0338_6.nsv", "result0338_7.nsv", "result0338_8.nsv", "result0338_9.nsv", "result0338_10.nsv", "result0338_11.nsv", "result0338_12.nsv", "result0338_13.nsv", "result0338_14.nsv", "result0338_15.nsv", "result0338_16.nsv", "result0338_17.nsv", "result0338_18.nsv", "result0338_19.nsv"];
val thyn = "vfmTestDefs0338";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
