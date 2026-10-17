Theory vfmTest0290[no_sig_docs]
Ancestors vfmTestDefs0290
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0290_0.nsv", "result0290_1.nsv", "result0290_2.nsv", "result0290_3.nsv", "result0290_4.nsv", "result0290_5.nsv", "result0290_6.nsv", "result0290_7.nsv", "result0290_8.nsv", "result0290_9.nsv", "result0290_10.nsv", "result0290_11.nsv", "result0290_12.nsv", "result0290_13.nsv", "result0290_14.nsv", "result0290_15.nsv", "result0290_16.nsv", "result0290_17.nsv", "result0290_18.nsv", "result0290_19.nsv", "result0290_20.nsv", "result0290_21.nsv", "result0290_22.nsv", "result0290_23.nsv", "result0290_24.nsv", "result0290_25.nsv", "result0290_26.nsv", "result0290_27.nsv", "result0290_28.nsv", "result0290_29.nsv"];
val thyn = "vfmTestDefs0290";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
