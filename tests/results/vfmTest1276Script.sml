Theory vfmTest1276[no_sig_docs]
Ancestors vfmTestDefs1276
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1276_0.nsv", "result1276_1.nsv", "result1276_2.nsv", "result1276_3.nsv", "result1276_4.nsv", "result1276_5.nsv", "result1276_6.nsv", "result1276_7.nsv", "result1276_8.nsv", "result1276_9.nsv", "result1276_10.nsv", "result1276_11.nsv", "result1276_12.nsv", "result1276_13.nsv", "result1276_14.nsv", "result1276_15.nsv", "result1276_16.nsv", "result1276_17.nsv", "result1276_18.nsv", "result1276_19.nsv", "result1276_20.nsv", "result1276_21.nsv", "result1276_22.nsv", "result1276_23.nsv", "result1276_24.nsv", "result1276_25.nsv", "result1276_26.nsv"];
val thyn = "vfmTestDefs1276";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
