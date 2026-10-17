Theory vfmTest2262[no_sig_docs]
Ancestors vfmTestDefs2262
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2262_0.nsv", "result2262_1.nsv", "result2262_2.nsv", "result2262_3.nsv", "result2262_4.nsv", "result2262_5.nsv", "result2262_6.nsv", "result2262_7.nsv", "result2262_8.nsv", "result2262_9.nsv", "result2262_10.nsv", "result2262_11.nsv", "result2262_12.nsv", "result2262_13.nsv", "result2262_14.nsv", "result2262_15.nsv", "result2262_16.nsv", "result2262_17.nsv", "result2262_18.nsv", "result2262_19.nsv", "result2262_20.nsv", "result2262_21.nsv", "result2262_22.nsv", "result2262_23.nsv", "result2262_24.nsv", "result2262_25.nsv", "result2262_26.nsv", "result2262_27.nsv", "result2262_28.nsv", "result2262_29.nsv", "result2262_30.nsv", "result2262_31.nsv", "result2262_32.nsv"];
val thyn = "vfmTestDefs2262";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
