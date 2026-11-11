Theory vfmTest2140[no_sig_docs]
Ancestors vfmTestDefs2140
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2140_0.nsv", "result2140_1.nsv", "result2140_2.nsv", "result2140_3.nsv", "result2140_4.nsv", "result2140_5.nsv", "result2140_6.nsv", "result2140_7.nsv", "result2140_8.nsv", "result2140_9.nsv", "result2140_10.nsv", "result2140_11.nsv", "result2140_12.nsv", "result2140_13.nsv", "result2140_14.nsv", "result2140_15.nsv", "result2140_16.nsv", "result2140_17.nsv", "result2140_18.nsv", "result2140_19.nsv", "result2140_20.nsv", "result2140_21.nsv", "result2140_22.nsv", "result2140_23.nsv", "result2140_24.nsv", "result2140_25.nsv", "result2140_26.nsv", "result2140_27.nsv", "result2140_28.nsv", "result2140_29.nsv", "result2140_30.nsv", "result2140_31.nsv", "result2140_32.nsv", "result2140_33.nsv", "result2140_34.nsv", "result2140_35.nsv"];
val thyn = "vfmTestDefs2140";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
