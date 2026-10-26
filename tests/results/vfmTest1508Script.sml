Theory vfmTest1508[no_sig_docs]
Ancestors vfmTestDefs1508
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1508_0.nsv", "result1508_1.nsv", "result1508_2.nsv", "result1508_3.nsv", "result1508_4.nsv", "result1508_5.nsv", "result1508_6.nsv", "result1508_7.nsv", "result1508_8.nsv", "result1508_9.nsv", "result1508_10.nsv", "result1508_11.nsv", "result1508_12.nsv", "result1508_13.nsv", "result1508_14.nsv", "result1508_15.nsv", "result1508_16.nsv", "result1508_17.nsv", "result1508_18.nsv", "result1508_19.nsv", "result1508_20.nsv", "result1508_21.nsv", "result1508_22.nsv", "result1508_23.nsv", "result1508_24.nsv", "result1508_25.nsv", "result1508_26.nsv", "result1508_27.nsv", "result1508_28.nsv", "result1508_29.nsv", "result1508_30.nsv", "result1508_31.nsv"];
val thyn = "vfmTestDefs1508";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
