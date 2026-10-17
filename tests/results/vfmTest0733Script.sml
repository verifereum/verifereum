Theory vfmTest0733[no_sig_docs]
Ancestors vfmTestDefs0733
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0733_0.nsv", "result0733_1.nsv", "result0733_2.nsv", "result0733_3.nsv", "result0733_4.nsv", "result0733_5.nsv", "result0733_6.nsv", "result0733_7.nsv", "result0733_8.nsv", "result0733_9.nsv", "result0733_10.nsv", "result0733_11.nsv", "result0733_12.nsv", "result0733_13.nsv", "result0733_14.nsv", "result0733_15.nsv", "result0733_16.nsv", "result0733_17.nsv", "result0733_18.nsv", "result0733_19.nsv", "result0733_20.nsv", "result0733_21.nsv", "result0733_22.nsv", "result0733_23.nsv", "result0733_24.nsv", "result0733_25.nsv", "result0733_26.nsv", "result0733_27.nsv", "result0733_28.nsv", "result0733_29.nsv", "result0733_30.nsv", "result0733_31.nsv", "result0733_32.nsv", "result0733_33.nsv"];
val thyn = "vfmTestDefs0733";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
