Theory vfmTest0276[no_sig_docs]
Ancestors vfmTestDefs0276
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0276_0.nsv", "result0276_1.nsv", "result0276_2.nsv", "result0276_3.nsv", "result0276_4.nsv", "result0276_5.nsv", "result0276_6.nsv", "result0276_7.nsv", "result0276_8.nsv", "result0276_9.nsv", "result0276_10.nsv", "result0276_11.nsv", "result0276_12.nsv", "result0276_13.nsv", "result0276_14.nsv", "result0276_15.nsv", "result0276_16.nsv", "result0276_17.nsv", "result0276_18.nsv", "result0276_19.nsv", "result0276_20.nsv", "result0276_21.nsv", "result0276_22.nsv", "result0276_23.nsv", "result0276_24.nsv", "result0276_25.nsv", "result0276_26.nsv", "result0276_27.nsv", "result0276_28.nsv", "result0276_29.nsv", "result0276_30.nsv", "result0276_31.nsv"];
val thyn = "vfmTestDefs0276";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
