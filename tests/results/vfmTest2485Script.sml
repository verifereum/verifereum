Theory vfmTest2485[no_sig_docs]
Ancestors vfmTestDefs2485
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2485_0.nsv", "result2485_1.nsv", "result2485_2.nsv", "result2485_3.nsv", "result2485_4.nsv", "result2485_5.nsv", "result2485_6.nsv", "result2485_7.nsv", "result2485_8.nsv", "result2485_9.nsv", "result2485_10.nsv", "result2485_11.nsv", "result2485_12.nsv", "result2485_13.nsv", "result2485_14.nsv", "result2485_15.nsv", "result2485_16.nsv", "result2485_17.nsv", "result2485_18.nsv", "result2485_19.nsv", "result2485_20.nsv", "result2485_21.nsv", "result2485_22.nsv", "result2485_23.nsv", "result2485_24.nsv", "result2485_25.nsv", "result2485_26.nsv", "result2485_27.nsv", "result2485_28.nsv", "result2485_29.nsv", "result2485_30.nsv", "result2485_31.nsv"];
val thyn = "vfmTestDefs2485";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
