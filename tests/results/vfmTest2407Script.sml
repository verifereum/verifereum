Theory vfmTest2407[no_sig_docs]
Ancestors vfmTestDefs2407
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2407_0.nsv", "result2407_1.nsv", "result2407_2.nsv", "result2407_3.nsv", "result2407_4.nsv", "result2407_5.nsv", "result2407_6.nsv", "result2407_7.nsv", "result2407_8.nsv", "result2407_9.nsv", "result2407_10.nsv", "result2407_11.nsv", "result2407_12.nsv", "result2407_13.nsv", "result2407_14.nsv", "result2407_15.nsv", "result2407_16.nsv", "result2407_17.nsv", "result2407_18.nsv", "result2407_19.nsv", "result2407_20.nsv", "result2407_21.nsv", "result2407_22.nsv", "result2407_23.nsv", "result2407_24.nsv", "result2407_25.nsv", "result2407_26.nsv", "result2407_27.nsv", "result2407_28.nsv", "result2407_29.nsv"];
val thyn = "vfmTestDefs2407";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
