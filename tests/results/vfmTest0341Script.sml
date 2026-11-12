Theory vfmTest0341[no_sig_docs]
Ancestors vfmTestDefs0341
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0341_0.nsv", "result0341_1.nsv", "result0341_2.nsv", "result0341_3.nsv", "result0341_4.nsv", "result0341_5.nsv", "result0341_6.nsv", "result0341_7.nsv", "result0341_8.nsv", "result0341_9.nsv", "result0341_10.nsv", "result0341_11.nsv", "result0341_12.nsv", "result0341_13.nsv", "result0341_14.nsv", "result0341_15.nsv", "result0341_16.nsv", "result0341_17.nsv", "result0341_18.nsv", "result0341_19.nsv", "result0341_20.nsv", "result0341_21.nsv", "result0341_22.nsv", "result0341_23.nsv", "result0341_24.nsv", "result0341_25.nsv", "result0341_26.nsv", "result0341_27.nsv", "result0341_28.nsv", "result0341_29.nsv"];
val thyn = "vfmTestDefs0341";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
