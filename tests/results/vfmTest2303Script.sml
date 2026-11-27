Theory vfmTest2303[no_sig_docs]
Ancestors vfmTestDefs2303
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2303_0.nsv", "result2303_1.nsv", "result2303_2.nsv", "result2303_3.nsv", "result2303_4.nsv", "result2303_5.nsv", "result2303_6.nsv", "result2303_7.nsv", "result2303_8.nsv", "result2303_9.nsv", "result2303_10.nsv", "result2303_11.nsv", "result2303_12.nsv", "result2303_13.nsv", "result2303_14.nsv", "result2303_15.nsv", "result2303_16.nsv", "result2303_17.nsv", "result2303_18.nsv", "result2303_19.nsv", "result2303_20.nsv", "result2303_21.nsv", "result2303_22.nsv", "result2303_23.nsv", "result2303_24.nsv", "result2303_25.nsv", "result2303_26.nsv", "result2303_27.nsv", "result2303_28.nsv", "result2303_29.nsv", "result2303_30.nsv", "result2303_31.nsv"];
val thyn = "vfmTestDefs2303";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
