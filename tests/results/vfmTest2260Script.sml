Theory vfmTest2260[no_sig_docs]
Ancestors vfmTestDefs2260
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2260_0.nsv", "result2260_1.nsv", "result2260_2.nsv", "result2260_3.nsv", "result2260_4.nsv", "result2260_5.nsv", "result2260_6.nsv", "result2260_7.nsv", "result2260_8.nsv", "result2260_9.nsv", "result2260_10.nsv", "result2260_11.nsv", "result2260_12.nsv", "result2260_13.nsv", "result2260_14.nsv", "result2260_15.nsv", "result2260_16.nsv", "result2260_17.nsv", "result2260_18.nsv", "result2260_19.nsv", "result2260_20.nsv", "result2260_21.nsv", "result2260_22.nsv", "result2260_23.nsv", "result2260_24.nsv", "result2260_25.nsv", "result2260_26.nsv", "result2260_27.nsv", "result2260_28.nsv", "result2260_29.nsv", "result2260_30.nsv", "result2260_31.nsv", "result2260_32.nsv", "result2260_33.nsv", "result2260_34.nsv", "result2260_35.nsv"];
val thyn = "vfmTestDefs2260";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
