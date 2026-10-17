Theory vfmTest0176[no_sig_docs]
Ancestors vfmTestDefs0176
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0176_0.nsv", "result0176_1.nsv", "result0176_2.nsv", "result0176_3.nsv", "result0176_4.nsv", "result0176_5.nsv", "result0176_6.nsv", "result0176_7.nsv", "result0176_8.nsv", "result0176_9.nsv", "result0176_10.nsv", "result0176_11.nsv", "result0176_12.nsv", "result0176_13.nsv", "result0176_14.nsv", "result0176_15.nsv", "result0176_16.nsv", "result0176_17.nsv", "result0176_18.nsv", "result0176_19.nsv", "result0176_20.nsv", "result0176_21.nsv", "result0176_22.nsv", "result0176_23.nsv", "result0176_24.nsv", "result0176_25.nsv", "result0176_26.nsv", "result0176_27.nsv", "result0176_28.nsv", "result0176_29.nsv", "result0176_30.nsv", "result0176_31.nsv"];
val thyn = "vfmTestDefs0176";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
