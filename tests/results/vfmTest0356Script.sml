Theory vfmTest0356[no_sig_docs]
Ancestors vfmTestDefs0356
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0356_0.nsv", "result0356_1.nsv", "result0356_2.nsv", "result0356_3.nsv", "result0356_4.nsv", "result0356_5.nsv", "result0356_6.nsv", "result0356_7.nsv", "result0356_8.nsv", "result0356_9.nsv", "result0356_10.nsv", "result0356_11.nsv", "result0356_12.nsv", "result0356_13.nsv", "result0356_14.nsv", "result0356_15.nsv", "result0356_16.nsv", "result0356_17.nsv", "result0356_18.nsv", "result0356_19.nsv", "result0356_20.nsv", "result0356_21.nsv", "result0356_22.nsv", "result0356_23.nsv", "result0356_24.nsv", "result0356_25.nsv", "result0356_26.nsv", "result0356_27.nsv", "result0356_28.nsv", "result0356_29.nsv"];
val thyn = "vfmTestDefs0356";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
