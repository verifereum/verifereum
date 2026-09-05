Theory vfmTest0229[no_sig_docs]
Ancestors vfmTestDefs0229
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0229_0.nsv", "result0229_1.nsv", "result0229_2.nsv", "result0229_3.nsv", "result0229_4.nsv", "result0229_5.nsv", "result0229_6.nsv", "result0229_7.nsv", "result0229_8.nsv", "result0229_9.nsv", "result0229_10.nsv", "result0229_11.nsv", "result0229_12.nsv", "result0229_13.nsv", "result0229_14.nsv", "result0229_15.nsv", "result0229_16.nsv", "result0229_17.nsv", "result0229_18.nsv", "result0229_19.nsv", "result0229_20.nsv", "result0229_21.nsv", "result0229_22.nsv", "result0229_23.nsv", "result0229_24.nsv", "result0229_25.nsv", "result0229_26.nsv", "result0229_27.nsv", "result0229_28.nsv", "result0229_29.nsv", "result0229_30.nsv", "result0229_31.nsv"];
val thyn = "vfmTestDefs0229";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
