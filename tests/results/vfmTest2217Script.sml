Theory vfmTest2217[no_sig_docs]
Ancestors vfmTestDefs2217
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2217_0.nsv", "result2217_1.nsv", "result2217_2.nsv", "result2217_3.nsv", "result2217_4.nsv", "result2217_5.nsv", "result2217_6.nsv", "result2217_7.nsv", "result2217_8.nsv", "result2217_9.nsv", "result2217_10.nsv", "result2217_11.nsv", "result2217_12.nsv", "result2217_13.nsv", "result2217_14.nsv", "result2217_15.nsv", "result2217_16.nsv", "result2217_17.nsv", "result2217_18.nsv", "result2217_19.nsv", "result2217_20.nsv", "result2217_21.nsv", "result2217_22.nsv", "result2217_23.nsv", "result2217_24.nsv", "result2217_25.nsv", "result2217_26.nsv", "result2217_27.nsv", "result2217_28.nsv", "result2217_29.nsv", "result2217_30.nsv", "result2217_31.nsv", "result2217_32.nsv"];
val thyn = "vfmTestDefs2217";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
