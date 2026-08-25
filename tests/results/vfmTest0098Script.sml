Theory vfmTest0098[no_sig_docs]
Ancestors vfmTestDefs0098
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0098_0.nsv", "result0098_1.nsv", "result0098_2.nsv", "result0098_3.nsv", "result0098_4.nsv", "result0098_5.nsv", "result0098_6.nsv", "result0098_7.nsv", "result0098_8.nsv", "result0098_9.nsv", "result0098_10.nsv", "result0098_11.nsv", "result0098_12.nsv", "result0098_13.nsv", "result0098_14.nsv", "result0098_15.nsv", "result0098_16.nsv", "result0098_17.nsv", "result0098_18.nsv", "result0098_19.nsv", "result0098_20.nsv", "result0098_21.nsv", "result0098_22.nsv", "result0098_23.nsv", "result0098_24.nsv", "result0098_25.nsv", "result0098_26.nsv", "result0098_27.nsv", "result0098_28.nsv", "result0098_29.nsv", "result0098_30.nsv", "result0098_31.nsv", "result0098_32.nsv", "result0098_33.nsv", "result0098_34.nsv", "result0098_35.nsv"];
val thyn = "vfmTestDefs0098";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
