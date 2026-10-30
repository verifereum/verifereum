Theory vfmTest1451[no_sig_docs]
Ancestors vfmTestDefs1451
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1451_0.nsv", "result1451_1.nsv", "result1451_2.nsv", "result1451_3.nsv", "result1451_4.nsv", "result1451_5.nsv", "result1451_6.nsv", "result1451_7.nsv", "result1451_8.nsv", "result1451_9.nsv", "result1451_10.nsv", "result1451_11.nsv", "result1451_12.nsv", "result1451_13.nsv", "result1451_14.nsv", "result1451_15.nsv", "result1451_16.nsv", "result1451_17.nsv", "result1451_18.nsv", "result1451_19.nsv", "result1451_20.nsv", "result1451_21.nsv", "result1451_22.nsv", "result1451_23.nsv", "result1451_24.nsv", "result1451_25.nsv", "result1451_26.nsv", "result1451_27.nsv", "result1451_28.nsv", "result1451_29.nsv", "result1451_30.nsv", "result1451_31.nsv", "result1451_32.nsv", "result1451_33.nsv", "result1451_34.nsv", "result1451_35.nsv", "result1451_36.nsv", "result1451_37.nsv"];
val thyn = "vfmTestDefs1451";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
