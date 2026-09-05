Theory vfmTest0730[no_sig_docs]
Ancestors vfmTestDefs0730
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0730_0.nsv", "result0730_1.nsv", "result0730_2.nsv", "result0730_3.nsv", "result0730_4.nsv", "result0730_5.nsv", "result0730_6.nsv", "result0730_7.nsv", "result0730_8.nsv", "result0730_9.nsv", "result0730_10.nsv", "result0730_11.nsv", "result0730_12.nsv", "result0730_13.nsv", "result0730_14.nsv", "result0730_15.nsv", "result0730_16.nsv", "result0730_17.nsv", "result0730_18.nsv", "result0730_19.nsv", "result0730_20.nsv", "result0730_21.nsv", "result0730_22.nsv", "result0730_23.nsv", "result0730_24.nsv", "result0730_25.nsv", "result0730_26.nsv", "result0730_27.nsv", "result0730_28.nsv", "result0730_29.nsv", "result0730_30.nsv", "result0730_31.nsv", "result0730_32.nsv", "result0730_33.nsv"];
val thyn = "vfmTestDefs0730";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
