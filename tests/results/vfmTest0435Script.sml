Theory vfmTest0435[no_sig_docs]
Ancestors vfmTestDefs0435
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0435_0.nsv", "result0435_1.nsv", "result0435_2.nsv", "result0435_3.nsv", "result0435_4.nsv", "result0435_5.nsv", "result0435_6.nsv", "result0435_7.nsv", "result0435_8.nsv", "result0435_9.nsv", "result0435_10.nsv", "result0435_11.nsv", "result0435_12.nsv", "result0435_13.nsv", "result0435_14.nsv", "result0435_15.nsv", "result0435_16.nsv", "result0435_17.nsv", "result0435_18.nsv", "result0435_19.nsv", "result0435_20.nsv", "result0435_21.nsv", "result0435_22.nsv", "result0435_23.nsv", "result0435_24.nsv", "result0435_25.nsv", "result0435_26.nsv"];
val thyn = "vfmTestDefs0435";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
