Theory vfmTest2335[no_sig_docs]
Ancestors vfmTestDefs2335
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2335_0.nsv", "result2335_1.nsv", "result2335_2.nsv", "result2335_3.nsv", "result2335_4.nsv", "result2335_5.nsv", "result2335_6.nsv", "result2335_7.nsv", "result2335_8.nsv", "result2335_9.nsv", "result2335_10.nsv", "result2335_11.nsv", "result2335_12.nsv", "result2335_13.nsv", "result2335_14.nsv", "result2335_15.nsv", "result2335_16.nsv", "result2335_17.nsv", "result2335_18.nsv", "result2335_19.nsv", "result2335_20.nsv", "result2335_21.nsv", "result2335_22.nsv", "result2335_23.nsv", "result2335_24.nsv", "result2335_25.nsv", "result2335_26.nsv", "result2335_27.nsv", "result2335_28.nsv", "result2335_29.nsv", "result2335_30.nsv", "result2335_31.nsv", "result2335_32.nsv", "result2335_33.nsv", "result2335_34.nsv", "result2335_35.nsv"];
val thyn = "vfmTestDefs2335";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
