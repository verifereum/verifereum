Theory vfmTest2411[no_sig_docs]
Ancestors vfmTestDefs2411
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2411_0.nsv", "result2411_1.nsv", "result2411_2.nsv", "result2411_3.nsv", "result2411_4.nsv", "result2411_5.nsv", "result2411_6.nsv", "result2411_7.nsv", "result2411_8.nsv", "result2411_9.nsv", "result2411_10.nsv", "result2411_11.nsv", "result2411_12.nsv", "result2411_13.nsv", "result2411_14.nsv", "result2411_15.nsv", "result2411_16.nsv", "result2411_17.nsv", "result2411_18.nsv", "result2411_19.nsv", "result2411_20.nsv", "result2411_21.nsv", "result2411_22.nsv", "result2411_23.nsv", "result2411_24.nsv", "result2411_25.nsv", "result2411_26.nsv", "result2411_27.nsv", "result2411_28.nsv", "result2411_29.nsv", "result2411_30.nsv", "result2411_31.nsv", "result2411_32.nsv", "result2411_33.nsv", "result2411_34.nsv", "result2411_35.nsv", "result2411_36.nsv", "result2411_37.nsv", "result2411_38.nsv", "result2411_39.nsv"];
val thyn = "vfmTestDefs2411";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
