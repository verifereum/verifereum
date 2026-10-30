Theory vfmTest1094[no_sig_docs]
Ancestors vfmTestDefs1094
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1094_0.nsv", "result1094_1.nsv", "result1094_2.nsv", "result1094_3.nsv", "result1094_4.nsv", "result1094_5.nsv", "result1094_6.nsv", "result1094_7.nsv", "result1094_8.nsv", "result1094_9.nsv", "result1094_10.nsv", "result1094_11.nsv", "result1094_12.nsv", "result1094_13.nsv", "result1094_14.nsv", "result1094_15.nsv", "result1094_16.nsv", "result1094_17.nsv", "result1094_18.nsv", "result1094_19.nsv", "result1094_20.nsv", "result1094_21.nsv", "result1094_22.nsv", "result1094_23.nsv", "result1094_24.nsv", "result1094_25.nsv", "result1094_26.nsv", "result1094_27.nsv", "result1094_28.nsv", "result1094_29.nsv", "result1094_30.nsv", "result1094_31.nsv", "result1094_32.nsv", "result1094_33.nsv"];
val thyn = "vfmTestDefs1094";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
