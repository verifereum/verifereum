Theory vfmTest2144[no_sig_docs]
Ancestors vfmTestDefs2144
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2144_0.nsv", "result2144_1.nsv", "result2144_2.nsv", "result2144_3.nsv", "result2144_4.nsv", "result2144_5.nsv", "result2144_6.nsv", "result2144_7.nsv", "result2144_8.nsv", "result2144_9.nsv", "result2144_10.nsv", "result2144_11.nsv", "result2144_12.nsv", "result2144_13.nsv", "result2144_14.nsv", "result2144_15.nsv", "result2144_16.nsv", "result2144_17.nsv", "result2144_18.nsv", "result2144_19.nsv", "result2144_20.nsv", "result2144_21.nsv", "result2144_22.nsv", "result2144_23.nsv", "result2144_24.nsv", "result2144_25.nsv", "result2144_26.nsv", "result2144_27.nsv", "result2144_28.nsv", "result2144_29.nsv", "result2144_30.nsv", "result2144_31.nsv", "result2144_32.nsv", "result2144_33.nsv", "result2144_34.nsv", "result2144_35.nsv"];
val thyn = "vfmTestDefs2144";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
