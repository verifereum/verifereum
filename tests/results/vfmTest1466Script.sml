Theory vfmTest1466[no_sig_docs]
Ancestors vfmTestDefs1466
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1466_0.nsv", "result1466_1.nsv", "result1466_2.nsv", "result1466_3.nsv", "result1466_4.nsv", "result1466_5.nsv", "result1466_6.nsv", "result1466_7.nsv", "result1466_8.nsv", "result1466_9.nsv", "result1466_10.nsv", "result1466_11.nsv", "result1466_12.nsv", "result1466_13.nsv", "result1466_14.nsv", "result1466_15.nsv", "result1466_16.nsv", "result1466_17.nsv", "result1466_18.nsv", "result1466_19.nsv", "result1466_20.nsv", "result1466_21.nsv", "result1466_22.nsv", "result1466_23.nsv", "result1466_24.nsv", "result1466_25.nsv", "result1466_26.nsv", "result1466_27.nsv", "result1466_28.nsv", "result1466_29.nsv", "result1466_30.nsv", "result1466_31.nsv", "result1466_32.nsv", "result1466_33.nsv"];
val thyn = "vfmTestDefs1466";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
