Theory vfmTest1323[no_sig_docs]
Ancestors vfmTestDefs1323
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1323_0.nsv", "result1323_1.nsv", "result1323_2.nsv", "result1323_3.nsv", "result1323_4.nsv", "result1323_5.nsv", "result1323_6.nsv", "result1323_7.nsv", "result1323_8.nsv", "result1323_9.nsv", "result1323_10.nsv", "result1323_11.nsv", "result1323_12.nsv", "result1323_13.nsv", "result1323_14.nsv", "result1323_15.nsv", "result1323_16.nsv", "result1323_17.nsv", "result1323_18.nsv", "result1323_19.nsv", "result1323_20.nsv", "result1323_21.nsv", "result1323_22.nsv", "result1323_23.nsv", "result1323_24.nsv", "result1323_25.nsv", "result1323_26.nsv", "result1323_27.nsv", "result1323_28.nsv", "result1323_29.nsv", "result1323_30.nsv", "result1323_31.nsv", "result1323_32.nsv", "result1323_33.nsv", "result1323_34.nsv", "result1323_35.nsv"];
val thyn = "vfmTestDefs1323";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
