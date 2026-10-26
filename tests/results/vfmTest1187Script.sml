Theory vfmTest1187[no_sig_docs]
Ancestors vfmTestDefs1187
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1187_0.nsv", "result1187_1.nsv", "result1187_2.nsv", "result1187_3.nsv", "result1187_4.nsv", "result1187_5.nsv", "result1187_6.nsv", "result1187_7.nsv", "result1187_8.nsv", "result1187_9.nsv", "result1187_10.nsv", "result1187_11.nsv", "result1187_12.nsv", "result1187_13.nsv", "result1187_14.nsv", "result1187_15.nsv", "result1187_16.nsv", "result1187_17.nsv", "result1187_18.nsv", "result1187_19.nsv", "result1187_20.nsv", "result1187_21.nsv", "result1187_22.nsv", "result1187_23.nsv", "result1187_24.nsv", "result1187_25.nsv", "result1187_26.nsv", "result1187_27.nsv", "result1187_28.nsv", "result1187_29.nsv"];
val thyn = "vfmTestDefs1187";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
