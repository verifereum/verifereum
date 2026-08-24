Theory vfmTest0159[no_sig_docs]
Ancestors vfmTestDefs0159
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0159_0.nsv", "result0159_1.nsv", "result0159_2.nsv", "result0159_3.nsv", "result0159_4.nsv", "result0159_5.nsv", "result0159_6.nsv", "result0159_7.nsv", "result0159_8.nsv", "result0159_9.nsv", "result0159_10.nsv", "result0159_11.nsv", "result0159_12.nsv", "result0159_13.nsv", "result0159_14.nsv", "result0159_15.nsv", "result0159_16.nsv", "result0159_17.nsv", "result0159_18.nsv", "result0159_19.nsv", "result0159_20.nsv", "result0159_21.nsv", "result0159_22.nsv", "result0159_23.nsv", "result0159_24.nsv", "result0159_25.nsv", "result0159_26.nsv", "result0159_27.nsv"];
val thyn = "vfmTestDefs0159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
