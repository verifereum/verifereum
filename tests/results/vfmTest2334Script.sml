Theory vfmTest2334[no_sig_docs]
Ancestors vfmTestDefs2334
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2334_0.nsv", "result2334_1.nsv", "result2334_2.nsv", "result2334_3.nsv", "result2334_4.nsv", "result2334_5.nsv", "result2334_6.nsv", "result2334_7.nsv", "result2334_8.nsv", "result2334_9.nsv", "result2334_10.nsv", "result2334_11.nsv", "result2334_12.nsv", "result2334_13.nsv", "result2334_14.nsv", "result2334_15.nsv", "result2334_16.nsv", "result2334_17.nsv", "result2334_18.nsv", "result2334_19.nsv", "result2334_20.nsv", "result2334_21.nsv", "result2334_22.nsv", "result2334_23.nsv", "result2334_24.nsv", "result2334_25.nsv", "result2334_26.nsv", "result2334_27.nsv", "result2334_28.nsv", "result2334_29.nsv", "result2334_30.nsv", "result2334_31.nsv", "result2334_32.nsv"];
val thyn = "vfmTestDefs2334";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
