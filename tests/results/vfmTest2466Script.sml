Theory vfmTest2466[no_sig_docs]
Ancestors vfmTestDefs2466
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2466_0.nsv", "result2466_1.nsv", "result2466_2.nsv", "result2466_3.nsv", "result2466_4.nsv", "result2466_5.nsv", "result2466_6.nsv", "result2466_7.nsv", "result2466_8.nsv", "result2466_9.nsv", "result2466_10.nsv", "result2466_11.nsv", "result2466_12.nsv", "result2466_13.nsv", "result2466_14.nsv", "result2466_15.nsv", "result2466_16.nsv", "result2466_17.nsv", "result2466_18.nsv", "result2466_19.nsv", "result2466_20.nsv", "result2466_21.nsv", "result2466_22.nsv", "result2466_23.nsv", "result2466_24.nsv", "result2466_25.nsv", "result2466_26.nsv", "result2466_27.nsv", "result2466_28.nsv", "result2466_29.nsv", "result2466_30.nsv", "result2466_31.nsv", "result2466_32.nsv", "result2466_33.nsv", "result2466_34.nsv", "result2466_35.nsv", "result2466_36.nsv", "result2466_37.nsv", "result2466_38.nsv", "result2466_39.nsv"];
val thyn = "vfmTestDefs2466";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
