Theory vfmTest0870[no_sig_docs]
Ancestors vfmTestDefs0870
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0870_0.nsv", "result0870_1.nsv", "result0870_2.nsv", "result0870_3.nsv", "result0870_4.nsv", "result0870_5.nsv", "result0870_6.nsv", "result0870_7.nsv", "result0870_8.nsv", "result0870_9.nsv", "result0870_10.nsv", "result0870_11.nsv", "result0870_12.nsv", "result0870_13.nsv", "result0870_14.nsv", "result0870_15.nsv", "result0870_16.nsv", "result0870_17.nsv", "result0870_18.nsv", "result0870_19.nsv", "result0870_20.nsv", "result0870_21.nsv", "result0870_22.nsv", "result0870_23.nsv", "result0870_24.nsv", "result0870_25.nsv", "result0870_26.nsv", "result0870_27.nsv", "result0870_28.nsv", "result0870_29.nsv", "result0870_30.nsv", "result0870_31.nsv", "result0870_32.nsv", "result0870_33.nsv", "result0870_34.nsv", "result0870_35.nsv", "result0870_36.nsv", "result0870_37.nsv", "result0870_38.nsv", "result0870_39.nsv"];
val thyn = "vfmTestDefs0870";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
