Theory vfmTest2326[no_sig_docs]
Ancestors vfmTestDefs2326
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2326_0.nsv", "result2326_1.nsv", "result2326_2.nsv", "result2326_3.nsv", "result2326_4.nsv", "result2326_5.nsv", "result2326_6.nsv", "result2326_7.nsv", "result2326_8.nsv", "result2326_9.nsv", "result2326_10.nsv", "result2326_11.nsv", "result2326_12.nsv", "result2326_13.nsv", "result2326_14.nsv", "result2326_15.nsv", "result2326_16.nsv", "result2326_17.nsv", "result2326_18.nsv", "result2326_19.nsv", "result2326_20.nsv", "result2326_21.nsv", "result2326_22.nsv", "result2326_23.nsv", "result2326_24.nsv", "result2326_25.nsv", "result2326_26.nsv", "result2326_27.nsv", "result2326_28.nsv", "result2326_29.nsv", "result2326_30.nsv", "result2326_31.nsv", "result2326_32.nsv", "result2326_33.nsv", "result2326_34.nsv"];
val thyn = "vfmTestDefs2326";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
