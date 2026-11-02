Theory vfmTest0109[no_sig_docs]
Ancestors vfmTestDefs0109
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0109_0.nsv", "result0109_1.nsv", "result0109_2.nsv", "result0109_3.nsv", "result0109_4.nsv", "result0109_5.nsv", "result0109_6.nsv", "result0109_7.nsv", "result0109_8.nsv", "result0109_9.nsv", "result0109_10.nsv", "result0109_11.nsv", "result0109_12.nsv", "result0109_13.nsv", "result0109_14.nsv", "result0109_15.nsv", "result0109_16.nsv", "result0109_17.nsv", "result0109_18.nsv", "result0109_19.nsv", "result0109_20.nsv", "result0109_21.nsv", "result0109_22.nsv", "result0109_23.nsv", "result0109_24.nsv", "result0109_25.nsv", "result0109_26.nsv"];
val thyn = "vfmTestDefs0109";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
