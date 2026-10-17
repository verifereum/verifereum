Theory vfmTest0709[no_sig_docs]
Ancestors vfmTestDefs0709
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0709_0.nsv", "result0709_1.nsv", "result0709_2.nsv", "result0709_3.nsv", "result0709_4.nsv", "result0709_5.nsv", "result0709_6.nsv", "result0709_7.nsv", "result0709_8.nsv", "result0709_9.nsv", "result0709_10.nsv", "result0709_11.nsv", "result0709_12.nsv", "result0709_13.nsv", "result0709_14.nsv", "result0709_15.nsv", "result0709_16.nsv", "result0709_17.nsv", "result0709_18.nsv", "result0709_19.nsv", "result0709_20.nsv", "result0709_21.nsv", "result0709_22.nsv", "result0709_23.nsv"];
val thyn = "vfmTestDefs0709";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
