Theory vfmTest1079[no_sig_docs]
Ancestors vfmTestDefs1079
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1079_0.nsv", "result1079_1.nsv", "result1079_2.nsv", "result1079_3.nsv", "result1079_4.nsv", "result1079_5.nsv", "result1079_6.nsv", "result1079_7.nsv", "result1079_8.nsv", "result1079_9.nsv", "result1079_10.nsv", "result1079_11.nsv", "result1079_12.nsv", "result1079_13.nsv", "result1079_14.nsv", "result1079_15.nsv", "result1079_16.nsv", "result1079_17.nsv", "result1079_18.nsv", "result1079_19.nsv", "result1079_20.nsv", "result1079_21.nsv", "result1079_22.nsv", "result1079_23.nsv", "result1079_24.nsv", "result1079_25.nsv", "result1079_26.nsv", "result1079_27.nsv", "result1079_28.nsv", "result1079_29.nsv"];
val thyn = "vfmTestDefs1079";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
