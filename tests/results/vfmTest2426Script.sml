Theory vfmTest2426[no_sig_docs]
Ancestors vfmTestDefs2426
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2426_0.nsv", "result2426_1.nsv", "result2426_2.nsv", "result2426_3.nsv", "result2426_4.nsv", "result2426_5.nsv", "result2426_6.nsv", "result2426_7.nsv", "result2426_8.nsv", "result2426_9.nsv", "result2426_10.nsv", "result2426_11.nsv", "result2426_12.nsv", "result2426_13.nsv", "result2426_14.nsv", "result2426_15.nsv", "result2426_16.nsv", "result2426_17.nsv", "result2426_18.nsv", "result2426_19.nsv", "result2426_20.nsv", "result2426_21.nsv", "result2426_22.nsv", "result2426_23.nsv", "result2426_24.nsv", "result2426_25.nsv", "result2426_26.nsv", "result2426_27.nsv", "result2426_28.nsv", "result2426_29.nsv", "result2426_30.nsv", "result2426_31.nsv"];
val thyn = "vfmTestDefs2426";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
