Theory vfmTest0712[no_sig_docs]
Ancestors vfmTestDefs0712
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0712_0.nsv", "result0712_1.nsv", "result0712_2.nsv", "result0712_3.nsv", "result0712_4.nsv", "result0712_5.nsv", "result0712_6.nsv", "result0712_7.nsv", "result0712_8.nsv", "result0712_9.nsv", "result0712_10.nsv", "result0712_11.nsv", "result0712_12.nsv", "result0712_13.nsv", "result0712_14.nsv", "result0712_15.nsv", "result0712_16.nsv", "result0712_17.nsv", "result0712_18.nsv", "result0712_19.nsv", "result0712_20.nsv", "result0712_21.nsv", "result0712_22.nsv", "result0712_23.nsv", "result0712_24.nsv", "result0712_25.nsv", "result0712_26.nsv", "result0712_27.nsv", "result0712_28.nsv", "result0712_29.nsv", "result0712_30.nsv", "result0712_31.nsv", "result0712_32.nsv", "result0712_33.nsv", "result0712_34.nsv", "result0712_35.nsv", "result0712_36.nsv", "result0712_37.nsv"];
val thyn = "vfmTestDefs0712";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
