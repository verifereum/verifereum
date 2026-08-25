Theory vfmTest0009[no_sig_docs]
Ancestors vfmTestDefs0009
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0009_0.nsv", "result0009_1.nsv", "result0009_2.nsv", "result0009_3.nsv", "result0009_4.nsv", "result0009_5.nsv", "result0009_6.nsv", "result0009_7.nsv", "result0009_8.nsv", "result0009_9.nsv", "result0009_10.nsv", "result0009_11.nsv", "result0009_12.nsv", "result0009_13.nsv", "result0009_14.nsv", "result0009_15.nsv", "result0009_16.nsv", "result0009_17.nsv", "result0009_18.nsv", "result0009_19.nsv", "result0009_20.nsv", "result0009_21.nsv", "result0009_22.nsv", "result0009_23.nsv", "result0009_24.nsv", "result0009_25.nsv", "result0009_26.nsv", "result0009_27.nsv", "result0009_28.nsv", "result0009_29.nsv", "result0009_30.nsv", "result0009_31.nsv", "result0009_32.nsv", "result0009_33.nsv", "result0009_34.nsv", "result0009_35.nsv", "result0009_36.nsv", "result0009_37.nsv", "result0009_38.nsv"];
val thyn = "vfmTestDefs0009";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
