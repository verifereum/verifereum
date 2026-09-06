Theory vfmTest2286[no_sig_docs]
Ancestors vfmTestDefs2286
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2286_0.nsv", "result2286_1.nsv", "result2286_2.nsv", "result2286_3.nsv", "result2286_4.nsv", "result2286_5.nsv", "result2286_6.nsv", "result2286_7.nsv", "result2286_8.nsv", "result2286_9.nsv", "result2286_10.nsv", "result2286_11.nsv", "result2286_12.nsv", "result2286_13.nsv", "result2286_14.nsv", "result2286_15.nsv", "result2286_16.nsv", "result2286_17.nsv", "result2286_18.nsv", "result2286_19.nsv", "result2286_20.nsv", "result2286_21.nsv", "result2286_22.nsv", "result2286_23.nsv", "result2286_24.nsv", "result2286_25.nsv", "result2286_26.nsv", "result2286_27.nsv", "result2286_28.nsv", "result2286_29.nsv", "result2286_30.nsv", "result2286_31.nsv", "result2286_32.nsv"];
val thyn = "vfmTestDefs2286";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
