Theory vfmTest1110[no_sig_docs]
Ancestors vfmTestDefs1110
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1110_0.nsv", "result1110_1.nsv", "result1110_2.nsv", "result1110_3.nsv", "result1110_4.nsv", "result1110_5.nsv", "result1110_6.nsv", "result1110_7.nsv", "result1110_8.nsv", "result1110_9.nsv", "result1110_10.nsv", "result1110_11.nsv", "result1110_12.nsv", "result1110_13.nsv", "result1110_14.nsv", "result1110_15.nsv", "result1110_16.nsv", "result1110_17.nsv", "result1110_18.nsv", "result1110_19.nsv", "result1110_20.nsv", "result1110_21.nsv", "result1110_22.nsv", "result1110_23.nsv", "result1110_24.nsv", "result1110_25.nsv", "result1110_26.nsv", "result1110_27.nsv", "result1110_28.nsv", "result1110_29.nsv", "result1110_30.nsv", "result1110_31.nsv"];
val thyn = "vfmTestDefs1110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
